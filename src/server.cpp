/*
Minetest - Modified for Full Mod Download Support
Copyright (C) 2010-2013 celeron55, Perttu Ahola <celeron55@gmail.com>
Modified for research purposes under Project OLYMP
*/

#include "server.h"
#include <iostream>
#include <queue>
#include <algorithm>
#include <zip.h>
#include <fstream>
#include "network/connection.h"
#include "network/networkprotocol.h"
#include "network/serveropcodes.h"
#include "ban.h"
#include "environment.h"
#include "map.h"
#include "threading/mutex_auto_lock.h"
#include "constants.h"
#include "voxel.h"
#include "config.h"
#include "version.h"
#include "filesys.h"
#include "mapblock.h"
#include "serverobject.h"
#include "genericobject.h"
#include "settings.h"
#include "profiler.h"
#include "log.h"
#include "scripting_server.h"
#include "nodedef.h"
#include "itemdef.h"
#include "craftdef.h"
#include "emerge.h"
#include "mapgen/mapgen.h"
#include "mapgen/mg_biome.h"
#include "content_mapnode.h"
#include "content_nodemeta.h"
#include "content_sao.h"
#include "content/mods.h"
#include "modchannels.h"
#include "serverlist.h"
#include "util/string.h"
#include "rollback.h"
#include "util/serialize.h"
#include "util/thread.h"
#include "defaultsettings.h"
#include "server/mods.h"
#include "util/base64.h"
#include "util/sha1.h"
#include "util/hex.h"
#include "database/database.h"
#include "chatmessage.h"
#include "chat_interface.h"
#include "remoteplayer.h"

// Новые константы для передачи модов
#define TOCLIENT_MOD_DATA 0x50
#define TOCLIENT_MOD_ANNOUNCE 0x51
#define TOSERVER_MOD_REQUEST 0x52
#define MAX_MOD_CHUNK_SIZE 32768

class ClientNotFoundException : public BaseException
{
public:
	ClientNotFoundException(const char *s):
		BaseException(s)
	{}
};

class ServerThread : public Thread
{
public:
	ServerThread(Server *server):
		Thread("Server"),
		m_server(server)
	{}
	void *run();
private:
	Server *m_server;
};

void *ServerThread::run()
{
	BEGIN_DEBUG_EXCEPTION_HANDLER
	m_server->AsyncRunStep(true);
	while (!stopRequested()) {
		try {
			m_server->AsyncRunStep();
			m_server->Receive();
		} catch (con::PeerNotFoundException &e) {
			infostream<<"Server: PeerNotFoundException"<<std::endl;
		} catch (ClientNotFoundException &e) {
		} catch (con::ConnectionBindFailed &e) {
			m_server->setAsyncFatalError(e.what());
		} catch (LuaError &e) {
			m_server->setAsyncFatalError(
					"ServerThread::run Lua: " + std::string(e.what()));
		}
	}
	END_DEBUG_EXCEPTION_HANDLER
	return nullptr;
}

v3f ServerSoundParams::getPos(ServerEnvironment *env, bool *pos_exists) const
{
	if(pos_exists) *pos_exists = false;
	switch(type){
	case SSP_LOCAL:
		return v3f(0,0,0);
	case SSP_POSITIONAL:
		if(pos_exists) *pos_exists = true;
		return pos;
	case SSP_OBJECT: {
		if(object == 0)
			return v3f(0,0,0);
		ServerActiveObject *sao = env->getActiveObject(object);
		if(!sao)
			return v3f(0,0,0);
		if(pos_exists) *pos_exists = true;
		return sao->getBasePosition(); }
	}
	return v3f(0,0,0);
}

void Server::ShutdownState::reset()
{
	m_timer = 0.0f;
	message.clear();
	should_reconnect = false;
	is_requested = false;
}

void Server::ShutdownState::trigger(float delay, const std::string &msg, bool reconnect)
{
	m_timer = delay;
	message = msg;
	should_reconnect = reconnect;
}

void Server::ShutdownState::tick(float dtime, Server *server)
{
	if (m_timer <= 0.0f)
		return;
	static const float shutdown_msg_times[] =
	{
		1, 2, 3, 4, 5, 10, 20, 40, 60, 120, 180, 300, 600, 1200, 1800, 3600
	};
	if (m_timer < shutdown_msg_times[ARRLEN(shutdown_msg_times) - 1]) {
		for (float t : shutdown_msg_times) {
			if (m_timer > t && m_timer - dtime < t) {
				std::wstring periodicMsg = getShutdownTimerMessage();
				infostream << wide_to_utf8(periodicMsg).c_str() << std::endl;
				server->SendChatMessage(PEER_ID_INEXISTENT, periodicMsg);
				break;
			}
		}
	}
	m_timer -= dtime;
	if (m_timer < 0.0f) {
		m_timer = 0.0f;
		is_requested = true;
	}
}

std::wstring Server::ShutdownState::getShutdownTimerMessage() const
{
	std::wstringstream ws;
	ws << L"*** Server shutting down in "
		<< duration_to_string(myround(m_timer)).c_str() << ".";
	return ws.str();
}

/*
	Server
*/

Server::Server(
		const std::string &path_world,
		const SubgameSpec &gamespec,
		bool simple_singleplayer_mode,
		Address bind_addr,
		bool dedicated,
		ChatInterface *iface
	):
	m_bind_addr(bind_addr),
	m_path_world(path_world),
	m_gamespec(gamespec),
	m_simple_singleplayer_mode(simple_singleplayer_mode),
	m_dedicated(dedicated),
	m_async_fatal_error(""),
	m_con(std::make_shared<con::Connection>(PROTOCOL_ID,
			512,
			CONNECTION_TIMEOUT,
			m_bind_addr.isIPv6(),
			this)),
	m_itemdef(createItemDefManager()),
	m_nodedef(createNodeDefManager()),
	m_craftdef(createCraftDefManager()),
	m_thread(new ServerThread(this)),
	m_uptime(0),
	m_clients(m_con),
	m_admin_chat(iface),
	m_modchannel_mgr(new ModChannelMgr())
{
	m_lag = g_settings->getFloat("dedicated_server_step");
	if (m_path_world.empty())
		throw ServerError("Supplied empty world path");
	if (!gamespec.isValid())
		throw ServerError("Supplied invalid gamespec");
	
	// Инициализация кэша модов
	initModCache();
}

Server::~Server()
{
	SendChatMessage(PEER_ID_INEXISTENT, ChatMessage(CHATMESSAGE_TYPE_ANNOUNCE,
			L"*** Server shutting down"));
	if (m_env) {
		MutexAutoLock envlock(m_env_mutex);
		infostream << "Server: Saving players" << std::endl;
		m_env->saveLoadedPlayers();
		infostream << "Server: Kicking players" << std::endl;
		std::string kick_msg;
		bool reconnect = false;
		if (isShutdownRequested()) {
			reconnect = m_shutdown_state.should_reconnect;
			kick_msg = m_shutdown_state.message;
		}
		if (kick_msg.empty()) {
			kick_msg = g_settings->get("kick_msg_shutdown");
		}
		m_env->saveLoadedPlayers(true);
		m_env->kickAllPlayers(SERVER_ACCESSDENIED_SHUTDOWN,
			kick_msg, reconnect);
	}
	actionstream << "Server: Shutting down" << std::endl;
	if (m_emerge)
		m_emerge->stopThreads();
	if (m_env) {
		MutexAutoLock envlock(m_env_mutex);
		infostream << "Executing shutdown hooks" << std::endl;
		m_script->on_shutdown();
		infostream << "Server: Saving environment metadata" << std::endl;
		m_env->saveMeta();
	}
	if (m_thread) {
		stop();
		delete m_thread;
	}
	delete m_emerge;
	delete m_env;
	delete m_rollback;
	delete m_banmanager;
	delete m_itemdef;
	delete m_nodedef;
	delete m_craftdef;
	delete m_script;
	for (auto &detached_inventory : m_detached_inventories) {
		delete detached_inventory.second;
	}
	while (!m_unsent_map_edit_queue.empty()) {
		delete m_unsent_map_edit_queue.front();
		m_unsent_map_edit_queue.pop();
	}
	
	// Очистка кэша модов
	for (auto &mod : m_mod_cache) {
		delete[] mod.second.data;
	}
	m_mod_cache.clear();
}

void Server::init()
{
	infostream << "Server created for gameid \"" << m_gamespec.id << "\"";
	if (m_simple_singleplayer_mode)
		infostream << " in simple singleplayer mode" << std::endl;
	else
		infostream << std::endl;
	infostream << "- world:  " << m_path_world << std::endl;
	infostream << "- game:   " << m_gamespec.path << std::endl;
	if (!loadGameConfAndInitWorld(m_path_world, m_gamespec))
		throw ServerError("Failed to initialize world");
	m_emerge = new EmergeManager(this);
	std::string ban_path = m_path_world + DIR_DELIM "ipban.txt";
	m_banmanager = new BanManager(ban_path);
	m_modmgr = std::unique_ptr<ServerModManager>(new ServerModManager(m_path_world));
	std::vector<ModSpec> unsatisfied_mods = m_modmgr->getUnsatisfiedMods();
	if (!m_modmgr->isConsistent()) {
		m_modmgr->printUnsatisfiedModsError();
	}
	MutexAutoLock envlock(m_env_mutex);
	ServerMap *servermap = new ServerMap(m_path_world, this, m_emerge);
	infostream << "Server: Initializing Lua" << std::endl;
	m_script = new ServerScripting(this);
	m_script->loadMod(getBuiltinLuaPath() + DIR_DELIM "init.lua", BUILTIN_MOD_NAME);
	m_modmgr->loadMods(m_script);
	fillMediaCache();
	m_nodedef->updateAliases(m_itemdef);
	std::vector<std::string> paths;
	fs::GetRecursiveDirs(paths, g_settings->get("texture_path"));
	fs::GetRecursiveDirs(paths, m_gamespec.path + DIR_DELIM + "textures");
	for (const std::string &path : paths)
		m_nodedef->applyTextureOverrides(path + DIR_DELIM + "override.txt");
	m_nodedef->setNodeRegistrationStatus(true);
	m_nodedef->runNodeResolveCallbacks();
	m_nodedef->mapNodeboxConnections();
	m_craftdef->initHashes(this);
	m_env = new ServerEnvironment(servermap, m_script, this, m_path_world);
	m_clients.setEnv(m_env);
	if (!servermap->settings_mgr.makeMapgenParams())
		FATAL_ERROR("Couldn't create any mapgen type");
	m_emerge->initMapgens(servermap->getMapgenParams());
	if (g_settings->getBool("enable_rollback_recording")) {
		m_rollback = new RollbackManager(m_path_world, this);
	}
	m_script->initializeEnvironment(m_env);
	servermap->addEventReceiver(this);
	m_env->loadMeta();
	m_liquid_transform_every = g_settings->getFloat("liquid_update");
	m_max_chatmessage_length = g_settings->getU16("chat_message_max_size");
	m_csm_restriction_flags = g_settings->getU64("csm_restriction_flags");
	m_csm_restriction_noderange = g_settings->getU32("csm_restriction_noderange");
	
	// Инициализация поддержки передачи модов
	enable_mod_transfer = g_settings->getBool("enable_mod_transfer");
	if (enable_mod_transfer) {
		infostream << "Server: Mod transfer enabled" << std::endl;
		prepareModPackages();
	}
}

void Server::initModCache()
{
	// Очистка существующего кэша
	m_mod_cache.clear();
	m_mod_manifests.clear();
}

void Server::prepareModPackages()
{
	infostream << "Server: Preparing mod packages for transfer" << std::endl;
	
	// Получаем список всех модов
	std::vector<ModSpec> mods = m_modmgr->getMods();
	
	for (const ModSpec &mod : mods) {
		// Пропускаем builtin моды
		if (mod.name == "builtin")
			continue;
			
		// Создаем ZIP архив мода
		std::string mod_path = mod.path;
		std::string mod_name = mod.name;
		std::string archive_path = m_path_world + DIR_DELIM + "mod_cache" + 
		                          DIR_DELIM + mod_name + ".zip";
		
		// Создаем директорию для кэша если её нет
		fs::CreateDir(m_path_world + DIR_DELIM + "mod_cache");
		
		// Создаем ZIP архив
		if (createModArchive(mod_path, archive_path)) {
			// Читаем архив в память
			std::ifstream file(archive_path, std::ios::binary | std::ios::ate);
			if (file.is_open()) {
				std::streamsize size = file.tellg();
				file.seekg(0, std::ios::beg);
				
				ModCacheEntry entry;
				entry.size = size;
				entry.data = new char[size];
				entry.mod_name = mod_name;
				entry.mod_path = mod_path;
				
				if (file.read(entry.data, size)) {
					// Вычисляем SHA1 хеш
					SHA1 sha1;
					sha1.addBytes(entry.data, size);
					unsigned char *digest = sha1.getDigest();
					entry.sha1 = base64_encode(digest, 20);
					free(digest);
					
					m_mod_cache[mod_name] = entry;
					
					// Создаем манифест
					ModManifest manifest;
					manifest.name = mod_name;
					manifest.size = size;
					manifest.sha1 = entry.sha1;
					manifest.depends = mod.depends;
					manifest.optdepends = mod.optdepends;
					m_mod_manifests[mod_name] = manifest;
					
					infostream << "Server: Cached mod '" << mod_name 
					          << "' size: " << size << " bytes" << std::endl;
				}
				file.close();
			}
		}
	}
	
	infostream << "Server: Prepared " << m_mod_cache.size() << " mods for transfer" << std::endl;
}

bool Server::createModArchive(const std::string &source_dir, const std::string &dest_file)
{
	// Используем libzip для создания архива
	int error = 0;
	zip_t *archive = zip_open(dest_file.c_str(), ZIP_CREATE | ZIP_TRUNCATE, &error);
	if (!archive) {
		errorstream << "Failed to create mod archive: " << dest_file << std::endl;
		return false;
	}
	
	// Рекурсивно добавляем файлы
	std::vector<std::string> files;
	fs::GetRecursiveDirs(files, source_dir);
	
	for (const std::string &file_path : files) {
		std::string relative_path = file_path.substr(source_dir.length() + 1);
		
		// Пропускаем некоторые файлы
		if (relative_path.find(".git") != std::string::npos ||
		    relative_path.find(".svn") != std::string::npos ||
		    relative_path.find("__pycache__") != std::string::npos)
			continue;
		
		// Читаем файл
		std::ifstream file(file_path, std::ios::binary);
		if (!file.good())
			continue;
			
		std::string content((std::istreambuf_iterator<char>(file)),
		                     std::istreambuf_iterator<char>());
		file.close();
		
		// Добавляем в архив
		zip_source_t *source = zip_source_buffer(archive, content.c_str(), content.size(), 0);
		if (source) {
			zip_file_add(archive, relative_path.c_str(), source, ZIP_FL_OVERWRITE);
		}
	}
	
	zip_close(archive);
	return true;
}

void Server::start()
{
	infostream << "Starting server on " << m_bind_addr.serializeString()
			<< "..." << std::endl;
	m_thread->stop();
	m_con->SetTimeoutMs(30);
	m_con->Serve(m_bind_addr);
	m_thread->start();
	std::cerr
		<< "        .__               __                   __   " << std::endl
		<< "  _____ |__| ____   _____/  |_  ____   _______/  |_ " << std::endl
		<< " /     \\|  |/    \\_/ __ \\   __\\/ __ \\ /  ___/\\   __\\" << std::endl
		<< "|  Y Y  \\  |   |  \\  ___/|  | \\  ___/ \\___ \\  |  |  " << std::endl
		<< "|__|_|  /__|___|  /\\___  >__|  \\___  >____  > |__|  " << std::endl
		<< "      \\/        \\/     \\/          \\/     \\/        " << std::endl;
	actionstream << "World at [" << m_path_world << "]" << std::endl;
	actionstream << "Server for gameid=\"" << m_gamespec.id
			<< "\" listening on " << m_bind_addr.serializeString() << ":"
			<< m_bind_addr.getPort() << "." << std::endl;
}

void Server::stop()
{
	infostream<<"Server: Stopping and waiting threads"<<std::endl;
	m_thread->stop();
	m_thread->wait();
	infostream<<"Server: Threads stopped"<<std::endl;
}

void Server::step(float dtime)
{
	if (dtime > 2.0)
		dtime = 2.0;
	{
		MutexAutoLock lock(m_step_dtime_mutex);
		m_step_dtime += dtime;
	}
	std::string async_err = m_async_fatal_error.get();
	if (!async_err.empty()) {
		if (!m_simple_singleplayer_mode) {
			m_env->kickAllPlayers(SERVER_ACCESSDENIED_CRASH,
				g_settings->get("kick_msg_crash"),
				g_settings->getBool("ask_reconnect_on_crash"));
		}
		throw ServerError("AsyncErr: " + async_err);
	}
}

void Server::AsyncRunStep(bool initial_step)
{
	float dtime;
	{
		MutexAutoLock lock1(m_step_dtime_mutex);
		dtime = m_step_dtime;
	}
	{
		SendBlocks(dtime);
	}
	if((dtime < 0.001) && !initial_step)
		return;
	ScopeProfiler sp(g_profiler, "Server::AsyncRunStep()", SPT_AVG);
	{
		MutexAutoLock lock1(m_step_dtime_mutex);
		m_step_dtime -= dtime;
	}
	{
		m_uptime.set(m_uptime.get() + dtime);
	}
	handlePeerChanges();
	m_env->setTimeOfDaySpeed(g_settings->getFloat("time_speed"));
	m_time_of_day_send_timer -= dtime;
	if(m_time_of_day_send_timer < 0.0) {
		m_time_of_day_send_timer = g_settings->getFloat("time_send_interval");
		u16 time = m_env->getTimeOfDay();
		float time_speed = g_settings->getFloat("time_speed");
		SendTimeOfDay(PEER_ID_INEXISTENT, time, time_speed);
	}
	{
		MutexAutoLock lock(m_env_mutex);
		float max_lag = m_env->getMaxLagEstimate();
		max_lag *= 0.9998;
		if(dtime > max_lag){
			if(dtime > 0.1 && dtime > max_lag * 2.0)
				infostream<<"Server: Maximum lag peaked to "<<dtime
						<<" s"<<std::endl;
			max_lag = dtime;
		}
		m_env->reportMaxLagEstimate(max_lag);
		m_env->step(dtime);
	}
	static const float map_timer_and_unload_dtime = 2.92;
	if(m_map_timer_and_unload_interval.step(dtime, map_timer_and_unload_dtime))
	{
		MutexAutoLock lock(m_env_mutex);
		ScopeProfiler sp(g_profiler, "Server: map timer and unload");
		m_env->getMap().timerUpdate(map_timer_and_unload_dtime,
			g_settings->getFloat("server_unload_unused_data_timeout"),
			U32_MAX);
	}
	if (m_admin_chat) {
		if (!m_admin_chat->command_queue.empty()) {
			MutexAutoLock lock(m_env_mutex);
			while (!m_admin_chat->command_queue.empty()) {
				ChatEvent *evt = m_admin_chat->command_queue.pop_frontNoEx();
				handleChatInterfaceEvent(evt);
				delete evt;
			}
		}
		m_admin_chat->outgoing_queue.push_back(
			new ChatEventTimeInfo(m_env->getGameTime(), m_env->getTimeOfDay()));
	}
	m_liquid_transform_timer += dtime;
	if(m_liquid_transform_timer >= m_liquid_transform_every)
	{
		m_liquid_transform_timer -= m_liquid_transform_every;
		MutexAutoLock lock(m_env_mutex);
		ScopeProfiler sp(g_profiler, "Server: liquid transform");
		std::map<v3s16, MapBlock*> modified_blocks;
		m_env->getMap().transformLiquids(modified_blocks, m_env);
		if (!modified_blocks.empty()) {
			SetBlocksNotSent(modified_blocks);
		}
	}
	m_clients.step(dtime);
	m_lag += (m_lag > dtime ? -1 : 1) * dtime/100;
#if USE_CURL
	{
		float &counter = m_masterserver_timer;
		if (!isSingleplayer() && (!counter || counter >= 300.0) &&
				g_settings->getBool("server_announce")) {
			ServerList::sendAnnounce(counter ? ServerList::AA_UPDATE :
						ServerList::AA_START,
					m_bind_addr.getPort(),
					m_clients.getPlayerNames(),
					m_uptime.get(),
					m_env->getGameTime(),
					m_lag,
					m_gamespec.id,
					Mapgen::getMapgenName(m_emerge->mgparams->mgtype),
					m_modmgr->getMods(),
					m_dedicated);
			counter = 0.01;
		}
		counter += dtime;
	}
#endif
	{
		MutexAutoLock envlock(m_env_mutex);
		m_clients.lock();
		const RemoteClientMap &clients = m_clients.getClientList();
		ScopeProfiler sp(g_profiler, "Server: update objects within range");
		for (const auto &client_it : clients) {
			RemoteClient *client = client_it.second;
			if (client->getState() < CS_DefinitionsSent)
				continue;
			if (!m_env->getPlayer(client->peer_id))
				continue;
			PlayerSAO *playersao = getPlayerSAO(client->peer_id);
			if (!playersao)
				continue;
			SendActiveObjectRemoveAdd(client, playersao);
		}
		m_clients.unlock();
		m_mod_storage_save_timer -= dtime;
		if (m_mod_storage_save_timer <= 0.0f) {
			infostream << "Saving registered mod storages." << std::endl;
			m_mod_storage_save_timer = g_settings->getFloat("server_map_save_interval");
			for (std::unordered_map<std::string, ModMetadata *>::const_iterator
				it = m_mod_storages.begin(); it != m_mod_storages.end(); ++it) {
				if (it->second->isModified()) {
					it->second->save(getModStoragePath());
				}
			}
		}
	}
	{
		MutexAutoLock envlock(m_env_mutex);
		ScopeProfiler sp(g_profiler, "Server: send SAO messages");
		std::unordered_map<u16, std::vector<ActiveObjectMessage>*> buffered_messages;
		for(;;) {
			ActiveObjectMessage aom = m_env->getActiveObjectMessage();
			if (aom.id == 0)
				break;
			std::vector<ActiveObjectMessage>* message_list = nullptr;
			std::unordered_map<u16, std::vector<ActiveObjectMessage>* >::iterator n;
			n = buffered_messages.find(aom.id);
			if (n == buffered_messages.end()) {
				message_list = new std::vector<ActiveObjectMessage>;
				buffered_messages[aom.id] = message_list;
			}
			else {
				message_list = n->second;
			}
			message_list->push_back(aom);
		}
		m_clients.lock();
		const RemoteClientMap &clients = m_clients.getClientList();
		for (const auto &client_it : clients) {
			RemoteClient *client = client_it.second;
			PlayerSAO *player = getPlayerSAO(client->peer_id);
			std::string reliable_data;
			std::string unreliable_data;
			for (const auto &buffered_message : buffered_messages) {
				u16 id = buffered_message.first;
				ServerActiveObject *sao = m_env->getActiveObject(id);
				if (!sao || client->m_known_objects.find(id) == client->m_known_objects.end())
					continue;
				std::vector<ActiveObjectMessage>* list = buffered_message.second;
				for (const ActiveObjectMessage &aom : *list) {
					if (aom.datastring[0] == GENERIC_CMD_UPDATE_POSITION) {
						if (sao->getId() == player->getId())
							continue;
						ServerActiveObject *parent = sao->getParent();
						if (parent && client->m_known_objects.find(parent->getId()) !=
								client->m_known_objects.end())
							continue;
					}
					std::string new_data;
					char buf[2];
					writeU16((u8*)&buf[0], aom.id);
					new_data.append(buf, 2);
					new_data += serializeString(aom.datastring);
					if (aom.reliable)
						reliable_data += new_data;
					else
						unreliable_data += new_data;
				}
			}
			if (!reliable_data.empty()) {
				SendActiveObjectMessages(client->peer_id, reliable_data);
			}
			if (!unreliable_data.empty()) {
				SendActiveObjectMessages(client->peer_id, unreliable_data, false);
			}
		}
		m_clients.unlock();
		for (auto &buffered_message : buffered_messages) {
			delete buffered_message.second;
		}
	}
	{
		MutexAutoLock lock(m_env_mutex);
		bool disable_single_change_sending = false;
		if(m_unsent_map_edit_queue.size() >= 4)
			disable_single_change_sending = true;
		int event_count = m_unsent_map_edit_queue.size();
		Profiler prof;
		std::list<v3s16> node_meta_updates;
		while (!m_unsent_map_edit_queue.empty()) {
			MapEditEvent* event = m_unsent_map_edit_queue.front();
			m_unsent_map_edit_queue.pop();
			std::unordered_set<u16> far_players;
			switch (event->type) {
			case MEET_ADDNODE:
			case MEET_SWAPNODE:
				prof.add("MEET_ADDNODE", 1);
				sendAddNode(event->p, event->n, &far_players,
						disable_single_change_sending ? 5 : 30,
						event->type == MEET_ADDNODE);
				break;
			case MEET_REMOVENODE:
				prof.add("MEET_REMOVENODE", 1);
				sendRemoveNode(event->p, &far_players,
						disable_single_change_sending ? 5 : 30);
				break;
			case MEET_BLOCK_NODE_METADATA_CHANGED: {
				verbosestream << "Server: MEET_BLOCK_NODE_METADATA_CHANGED" << std::endl;
				prof.add("MEET_BLOCK_NODE_METADATA_CHANGED", 1);
				if (!event->is_private_change) {
					node_meta_updates.remove(event->p);
					node_meta_updates.push_back(event->p);
				}
				if (MapBlock *block = m_env->getMap().getBlockNoCreateNoEx(
						getNodeBlockPos(event->p))) {
					block->raiseModified(MOD_STATE_WRITE_NEEDED,
						MOD_REASON_REPORT_META_CHANGE);
				}
				break;
			}
			case MEET_OTHER:
				infostream << "Server: MEET_OTHER" << std::endl;
				prof.add("MEET_OTHER", 1);
				for (const v3s16 &modified_block : event->modified_blocks) {
					m_clients.markBlockposAsNotSent(modified_block);
				}
				break;
			default:
				prof.add("unknown", 1);
				warningstream << "Server: Unknown MapEditEvent "
						<< ((u32)event->type) << std::endl;
				break;
			}
			if (!far_players.empty()) {
				std::map<v3s16, MapBlock*> modified_blocks2;
				for (const v3s16 &modified_block : event->modified_blocks) {
					modified_blocks2[modified_block] =
							m_env->getMap().getBlockNoCreateNoEx(modified_block);
				}
				for (const u16 far_player : far_players) {
					if (RemoteClient *client = getClient(far_player))
						client->SetBlocksNotSent(modified_blocks2);
				}
			}
			delete event;
		}
		if (event_count >= 5) {
			infostream << "Server: MapEditEvents:" << std::endl;
			prof.print(infostream);
		} else if (event_count != 0) {
			verbosestream << "Server: MapEditEvents:" << std::endl;
			prof.print(verbosestream);
		}
		if (node_meta_updates.size())
			sendMetadataChanged(node_meta_updates);
	}
	{
		float &counter = m_emergethread_trigger_timer;
		counter += dtime;
		if (counter >= 2.0) {
			counter = 0.0;
			m_emerge->startThreads();
		}
	}
	{
		float &counter = m_savemap_timer;
		counter += dtime;
		static thread_local const float save_interval =
			g_settings->getFloat("server_map_save_interval");
		if (counter >= save_interval) {
			counter = 0.0;
			MutexAutoLock lock(m_env_mutex);
			ScopeProfiler sp(g_profiler, "Server: map saving (sum)");
			if (m_banmanager->isModified()) {
				m_banmanager->save();
			}
			m_env->getMap().save(MOD_STATE_WRITE_NEEDED);
			m_env->saveLoadedPlayers();
			m_env->saveMeta();
		}
	}
	m_shutdown_state.tick(dtime, this);
	
	// Обработка запросов на передачу модов
	processModTransferQueue();
}

void Server::processModTransferQueue()
{
	MutexAutoLock lock(m_mod_transfer_mutex);
	
	auto it = m_mod_transfer_queue.begin();
	while (it != m_mod_transfer_queue.end()) {
		ModTransferRequest &request = *it;
		
		// Проверяем, не отключился ли клиент
		if (m_clients.getClientState(request.peer_id) < CS_Active) {
			it = m_mod_transfer_queue.erase(it);
			continue;
		}
		
		// Отправляем следующий чанк
		if (request.current_chunk < request.total_chunks) {
			sendModChunk(request.peer_id, request.mod_name, 
			            request.current_chunk, request.total_chunks);
			request.current_chunk++;
			it++;
		} else {
			// Передача завершена
			it = m_mod_transfer_queue.erase(it);
		}
	}
}

void Server::sendModChunk(session_t peer_id, const std::string &mod_name, 
                         u32 chunk_index, u32 total_chunks)
{
	auto it = m_mod_cache.find(mod_name);
	if (it == m_mod_cache.end()) {
		errorstream << "Mod not found in cache: " << mod_name << std::endl;
		return;
	}
	
	ModCacheEntry &entry = it->second;
	
	// Вычисляем смещение и размер чанка
	u32 offset = chunk_index * MAX_MOD_CHUNK_SIZE;
	u32 chunk_size = std::min(MAX_MOD_CHUNK_SIZE, entry.size - offset);
	
	NetworkPacket pkt(TOCLIENT_MOD_DATA, 0, peer_id);
	pkt << mod_name;
	pkt << total_chunks;
	pkt << chunk_index;
	pkt << chunk_size;
	pkt.putRawString(entry.data + offset, chunk_size);
	
	Send(&pkt);
	
	verbosestream << "Sent mod chunk " << (chunk_index + 1) << "/" << total_chunks 
	              << " for mod '" << mod_name << "' to peer " << peer_id << std::endl;
}

void Server::Receive()
{
	NetworkPacket pkt;
	session_t peer_id;
	bool first = true;
	for (;;) {
		pkt.clear();
		peer_id = 0;
		try {
			if (first) {
				m_con->Receive(&pkt);
				first = false;
			} else {
				if (!m_con->TryReceive(&pkt))
					return;
			}
			peer_id = pkt.getPeerId();
			ProcessData(&pkt);
		} catch (const con::InvalidIncomingDataException &e) {
			infostream << "Server::Receive(): InvalidIncomingDataException: what()="
					<< e.what() << std::endl;
		} catch (const SerializationError &e) {
			infostream << "Server::Receive(): SerializationError: what()="
					<< e.what() << std::endl;
		} catch (const ClientStateError &e) {
			errorstream << "ProcessData: peer=" << peer_id << " what()="
					 << e.what() << std::endl;
			DenyAccess_Legacy(peer_id, L"Your client sent something server didn't expect."
					L"Try reconnecting or updating your client");
		} catch (const con::PeerNotFoundException &e) {
		} catch (const con::NoIncomingDataException &e) {
			return;
		}
	}
}

PlayerSAO* Server::StageTwoClientInit(session_t peer_id)
{
	std::string playername;
	PlayerSAO *playersao = NULL;
	m_clients.lock();
	try {
		RemoteClient* client = m_clients.lockedGetClientNoEx(peer_id, CS_InitDone);
		if (client) {
			playername = client->getName();
			playersao = emergePlayer(playername.c_str(), peer_id, client->net_proto_version);
			
			// Отправляем клиенту информацию о доступных модах
			if (playersao && enable_mod_transfer) {
				sendModAnnouncement(peer_id);
			}
		}
	} catch (std::exception &e) {
		m_clients.unlock();
		throw;
	}
	m_clients.unlock();
	RemotePlayer *player = m_env->getPlayer(playername.c_str());
	if (!playersao || !player) {
		if (player && player->getPeerId() != PEER_ID_INEXISTENT) {
			actionstream << "Server: Failed to emerge player \"" << playername
					<< "\" (player allocated to an another client)" << std::endl;
			DenyAccess_Legacy(peer_id, L"Another client is connected with this "
					L"name. If your client closed unexpectedly, try again in "
					L"a minute.");
		} else {
			errorstream << "Server: " << playername << ": Failed to emerge player"
					<< std::endl;
			DenyAccess_Legacy(peer_id, L"Could not allocate player.");
		}
		return NULL;
	}
	SendMovePlayer(peer_id);
	SendPlayerPrivileges(peer_id);
	SendPlayerInventoryFormspec(peer_id);
	SendInventory(playersao, false);
	if (playersao->isDead())
		SendDeathscreen(peer_id, false, v3f(0,0,0));
	else
		SendPlayerHPOrDie(playersao,
				PlayerHPChangeReason(PlayerHPChangeReason::SET_HP));
	SendPlayerBreath(playersao);
	{
		Address addr = getPeerAddress(player->getPeerId());
		std::string ip_str = addr.serializeString();
		const std::vector<std::string> &names = m_clients.getPlayerNames();
		actionstream << player->getName() << " [" << ip_str << "] joins game. List of players: ";
		for (const std::string &name : names) {
			actionstream << name << " ";
		}
		actionstream << player->getName() <<std::endl;
	}
	return playersao;
}

void Server::sendModAnnouncement(session_t peer_id)
{
	if (!enable_mod_transfer || m_mod_manifests.empty())
		return;
		
	NetworkPacket pkt(TOCLIENT_MOD_ANNOUNCE, 0, peer_id);
	
	// Отправляем количество модов
	u16 mod_count = m_mod_manifests.size();
	pkt << mod_count;
	
	// Отправляем информацию о каждом моде
	for (const auto &manifest_pair : m_mod_manifests) {
		const ModManifest &manifest = manifest_pair.second;
		pkt << manifest.name;
		pkt << manifest.size;
		pkt << manifest.sha1;
		
		// Отправляем зависимости
		u16 dep_count = manifest.depends.size();
		pkt << dep_count;
		for (const std::string &dep : manifest.depends) {
			pkt << dep;
		}
		
		// Отправляем опциональные зависимости
		u16 optdep_count = manifest.optdepends.size();
		pkt << optdep_count;
		for (const std::string &optdep : manifest.optdepends) {
			pkt << optdep;
		}
	}
	
	Send(&pkt);
	infostream << "Sent mod announcement to peer " << peer_id 
	           << " (" << mod_count << " mods)" << std::endl;
}

inline void Server::handleCommand(NetworkPacket *pkt)
{
	const ToServerCommandHandler &opHandle = toServerCommandTable[pkt->getCommand()];
	(this->*opHandle.handler)(pkt);
}

void Server::ProcessData(NetworkPacket *pkt)
{
	MutexAutoLock envlock(m_env_mutex);
	ScopeProfiler sp(g_profiler, "Server: Process network packet (sum)");
	u32 peer_id = pkt->getPeerId();
	try {
		Address address = getPeerAddress(peer_id);
		std::string addr_s = address.serializeString();
		if(m_banmanager->isIpBanned(addr_s)) {
			std::string ban_name = m_banmanager->getBanName(addr_s);
			infostream << "Server: A banned client tried to connect from "
					<< addr_s << "; banned name was "
					<< ban_name << std::endl;
			DenyAccess_Legacy(peer_id, L"Your ip is banned. Banned name was "
					+ utf8_to_wide(ban_name));
			return;
		}
	}
	catch(con::PeerNotFoundException &e) {
		infostream << "Server::ProcessData(): Canceling: peer "
				<< peer_id << " not found" << std::endl;
		return;
	}
	try {
		ToServerCommand command = (ToServerCommand) pkt->getCommand();
		if (command >= TOSERVER_NUM_MSG_TYPES) {
			infostream << "Server: Ignoring unknown command "
					 << command << std::endl;
			return;
		}
		
		// Обработка новых команд для передачи модов
		if (command == TOSERVER_MOD_REQUEST) {
			handleModRequest(pkt);
			return;
		}
		
		if (toServerCommandTable[command].state == TOSERVER_STATE_NOT_CONNECTED) {
			handleCommand(pkt);
			return;
		}
		u8 peer_ser_ver = getClient(peer_id, CS_InitDone)->serialization_version;
		if(peer_ser_ver == SER_FMT_VER_INVALID) {
			errorstream << "Server::ProcessData(): Cancelling: Peer"
					" serialization format invalid or not initialized."
					" Skipping incoming command=" << command << std::endl;
			return;
		}
		if (toServerCommandTable[command].state == TOSERVER_STATE_STARTUP) {
			handleCommand(pkt);
			return;
		}
		if (m_clients.getClientState(peer_id) < CS_Active) {
			if (command == TOSERVER_PLAYERPOS) return;
			errorstream << "Got packet command: " << command << " for peer id "
					<< peer_id << " but client isn't active yet. Dropping packet "
					<< std::endl;
			return;
		}
		handleCommand(pkt);
	} catch (SendFailedException &e) {
		errorstream << "Server::ProcessData(): SendFailedException: "
				<< "what=" << e.what()
				<< std::endl;
	} catch (PacketError &e) {
		actionstream << "Server::ProcessData(): PacketError: "
				<< "what=" << e.what()
				<< std::endl;
	}
}

void Server::handleModRequest(NetworkPacket *pkt)
{
	session_t peer_id = pkt->getPeerId();
	
	std::string mod_name;
	u32 chunk_index;
	
	*pkt >> mod_name >> chunk_index;
	
	auto it = m_mod_cache.find(mod_name);
	if (it == m_mod_cache.end()) {
		errorstream << "Mod request for unknown mod: " << mod_name << " from peer " << peer_id << std::endl;
		return;
	}
	
	ModCacheEntry &entry = it->second;
	u32 total_chunks = (entry.size + MAX_MOD_CHUNK_SIZE - 1) / MAX_MOD_CHUNK_SIZE;
	
	// Добавляем запрос в очередь передачи
	MutexAutoLock lock(m_mod_transfer_mutex);
	
	ModTransferRequest request;
	request.peer_id = peer_id;
	request.mod_name = mod_name;
	request.current_chunk = chunk_index;
	request.total_chunks = total_chunks;
	
	m_mod_transfer_queue.push_back(request);
	
	infostream << "Added mod transfer request for '" << mod_name 
	           << "' from peer " << peer_id << " starting at chunk " << chunk_index << std::endl;
}

void Server::setTimeOfDay(u32 time)
{
	m_env->setTimeOfDay(time);
	m_time_of_day_send_timer = 0;
}

void Server::onMapEditEvent(const MapEditEvent &event)
{
	if (m_ignore_map_edit_events_area.contains(event.getArea()))
		return;
	m_unsent_map_edit_queue.push(new MapEditEvent(event));
}

Inventory* Server::getInventory(const InventoryLocation &loc)
{
	switch (loc.type) {
	case InventoryLocation::UNDEFINED:
	case InventoryLocation::CURRENT_PLAYER:
		break;
	case InventoryLocation::PLAYER:
	{
		RemotePlayer *player = m_env->getPlayer(loc.name.c_str());
		if(!player)
			return NULL;
		PlayerSAO *playersao = player->getPlayerSAO();
		if(!playersao)
			return NULL;
		return playersao->getInventory();
	}
		break;
	case InventoryLocation::NODEMETA:
	{
		NodeMetadata *meta = m_env->getMap().getNodeMetadata(loc.p);
		if(!meta)
			return NULL;
		return meta->getInventory();
	}
		break;
	case InventoryLocation::DETACHED:
	{
		if(m_detached_inventories.count(loc.name) == 0)
			return NULL;
		return m_detached_inventories[loc.name];
	}
		break;
	default:
		sanity_check(false);
		break;
	}
	return NULL;
}

void Server::setInventoryModified(const InventoryLocation &loc)
{
	switch(loc.type){
	case InventoryLocation::UNDEFINED:
		break;
	case InventoryLocation::PLAYER:
	{
		RemotePlayer *player = m_env->getPlayer(loc.name.c_str());
		if (!player)
			return;
		player->setModified(true);
		player->inventory.setModified(true);
	}
		break;
	case InventoryLocation::NODEMETA:
	{
		MapEditEvent event;
		event.type = MEET_BLOCK_NODE_METADATA_CHANGED;
		event.p = loc.p;
		m_env->getMap().dispatchEvent(event);
	}
		break;
	case InventoryLocation::DETACHED:
	{
	}
		break;
	default:
		sanity_check(false);
		break;
	}
}

void Server::SetBlocksNotSent(std::map<v3s16, MapBlock *>& block)
{
	std::vector<session_t> clients = m_clients.getClientIDs();
	m_clients.lock();
	for (const session_t client_id : clients) {
			if (RemoteClient *client = m_clients.lockedGetClientNoEx(client_id))
				client->SetBlocksNotSent(block);
	}
	m_clients.unlock();
}

void Server::peerAdded(con::Peer *peer)
{
	verbosestream<<"Server::peerAdded(): peer->id="
			<<peer->id<<std::endl;
	m_peer_change_queue.push(con::PeerChange(con::PEER_ADDED, peer->id, false));
}

void Server::deletingPeer(con::Peer *peer, bool timeout)
{
	verbosestream<<"Server::deletingPeer(): peer->id="
			<<peer->id<<", timeout="<<timeout<<std::endl;
	m_clients.event(peer->id, CSE_Disconnect);
	m_peer_change_queue.push(con::PeerChange(con::PEER_REMOVED, peer->id, timeout));
	
	// Удаляем запросы на передачу модов для этого пира
	MutexAutoLock lock(m_mod_transfer_mutex);
	auto it = m_mod_transfer_queue.begin();
	while (it != m_mod_transfer_queue.end()) {
		if (it->peer_id == peer->id) {
			it = m_mod_transfer_queue.erase(it);
		} else {
			++it;
		}
	}
}

bool Server::getClientConInfo(session_t peer_id, con::rtt_stat_type type, float* retval)
{
	*retval = m_con->getPeerStat(peer_id,type);
	return *retval != -1;
}

bool Server::getClientInfo(
		session_t    peer_id,
		ClientState* state,
		u32*         uptime,
		u8*          ser_vers,
		u16*         prot_vers,
		u8*          major,
		u8*          minor,
		u8*          patch,
		std::string* vers_string
	)
{
	*state = m_clients.getClientState(peer_id);
	m_clients.lock();
	RemoteClient* client = m_clients.lockedGetClientNoEx(peer_id, CS_Invalid);
	if (!client) {
		m_clients.unlock();
		return false;
	}
	*uptime = client->uptime();
	*ser_vers = client->serialization_version;
	*prot_vers = client->net_proto_version;
	*major = client->getMajor();
	*minor = client->getMinor();
	*patch = client->getPatch();
	*vers_string = client->getFull();
	m_clients.unlock();
	return true;
}

void Server::handlePeerChanges()
{
	while(!m_peer_change_queue.empty())
	{
		con::PeerChange c = m_peer_change_queue.front();
		m_peer_change_queue.pop();
		verbosestream<<"Server: Handling peer change: "
				<<"id="<<c.peer_id<<", timeout="<<c.timeout
				<<std::endl;
		switch(c.type)
		{
		case con::PEER_ADDED:
			m_clients.CreateClient(c.peer_id);
			break;
		case con::PEER_REMOVED:
			DeleteClient(c.peer_id, c.timeout?CDR_TIMEOUT:CDR_LEAVE);
			break;
		default:
			FATAL_ERROR("Invalid peer change event received!");
			break;
		}
	}
}

void Server::printToConsoleOnly(const std::string &text)
{
	if (m_admin_chat) {
		m_admin_chat->outgoing_queue.push_back(
			new ChatEventChat("", utf8_to_wide(text)));
	} else {
		std::cout << text << std::endl;
	}
}

void Server::Send(NetworkPacket *pkt)
{
	Send(pkt->getPeerId(), pkt);
}

void Server::Send(session_t peer_id, NetworkPacket *pkt)
{
	m_clients.send(peer_id,
		clientCommandFactoryTable[pkt->getCommand()].channel,
		pkt,
		clientCommandFactoryTable[pkt->getCommand()].reliable);
}

void Server::SendMovement(session_t peer_id)
{
	std::ostringstream os(std::ios_base::binary);
	NetworkPacket pkt(TOCLIENT_MOVEMENT, 12 * sizeof(float), peer_id);
	pkt << g_settings->getFloat("movement_acceleration_default");
	pkt << g_settings->getFloat("movement_acceleration_air");
	pkt << g_settings->getFloat("movement_acceleration_fast");
	pkt << g_settings->getFloat("movement_speed_walk");
	pkt << g_settings->getFloat("movement_speed_crouch");
	pkt << g_settings->getFloat("movement_speed_fast");
	pkt << g_settings->getFloat("movement_speed_climb");
	pkt << g_settings->getFloat("movement_speed_jump");
	pkt << g_settings->getFloat("movement_liquid_fluidity");
	pkt << g_settings->getFloat("movement_liquid_fluidity_smooth");
	pkt << g_settings->getFloat("movement_liquid_sink");
	pkt << g_settings->getFloat("movement_gravity");
	Send(&pkt);
}

void Server::SendPlayerHPOrDie(PlayerSAO *playersao, const PlayerHPChangeReason &reason)
{
	if (playersao->isImmortal())
		return;
	session_t peer_id = playersao->getPeerID();
	bool is_alive = playersao->getHP() > 0;
	if (is_alive)
		SendPlayerHP(peer_id);
	else
		DiePlayer(peer_id, reason);
}

void Server::SendHP(session_t peer_id, u16 hp)
{
	NetworkPacket pkt(TOCLIENT_HP, 1, peer_id);
	pkt << hp;
	Send(&pkt);
}

void Server::SendBreath(session_t peer_id, u16 breath)
{
	NetworkPacket pkt(TOCLIENT_BREATH, 2, peer_id);
	pkt << (u16) breath;
	Send(&pkt);
}

void Server::SendAccessDenied(session_t peer_id, AccessDeniedCode reason,
		const std::string &custom_reason, bool reconnect)
{
	assert(reason < SERVER_ACCESSDENIED_MAX);
	NetworkPacket pkt(TOCLIENT_ACCESS_DENIED, 1, peer_id);
	pkt << (u8)reason;
	if (reason == SERVER_ACCESSDENIED_CUSTOM_STRING)
		pkt << custom_reason;
	else if (reason == SERVER_ACCESSDENIED_SHUTDOWN ||
			reason == SERVER_ACCESSDENIED_CRASH)
		pkt << custom_reason << (u8)reconnect;
	Send(&pkt);
}

void Server::SendAccessDenied_Legacy(session_t peer_id,const std::wstring &reason)
{
	NetworkPacket pkt(TOCLIENT_ACCESS_DENIED_LEGACY, 0, peer_id);
	pkt << reason;
	Send(&pkt);
}

void Server::SendDeathscreen(session_t peer_id, bool set_camera_point_target,
		v3f camera_point_target)
{
	NetworkPacket pkt(TOCLIENT_DEATHSCREEN, 1 + sizeof(v3f), peer_id);
	pkt << set_camera_point_target << camera_point_target;
	Send(&pkt);
}

void Server::SendItemDef(session_t peer_id,
		IItemDefManager *itemdef, u16 protocol_version)
{
	NetworkPacket pkt(TOCLIENT_ITEMDEF, 0, peer_id);
	std::ostringstream tmp_os(std::ios::binary);
	itemdef->serialize(tmp_os, protocol_version);
	std::ostringstream tmp_os2(std::ios::binary);
	compressZlib(tmp_os.str(), tmp_os2);
	pkt.putLongString(tmp_os2.str());
	verbosestream << "Server: Sending item definitions to id(" << peer_id
			<< "): size=" << pkt.getSize() << std::endl;
	Send(&pkt);
}

void Server::SendNodeDef(session_t peer_id,
	const NodeDefManager *nodedef, u16 protocol_version)
{
	NetworkPacket pkt(TOCLIENT_NODEDEF, 0, peer_id);
	std::ostringstream tmp_os(std::ios::binary);
	nodedef->serialize(tmp_os, protocol_version);
	std::ostringstream tmp_os2(std::ios::binary);
	compressZlib(tmp_os.str(), tmp_os2);
	pkt.putLongString(tmp_os2.str());
	verbosestream << "Server: Sending node definitions to id(" << peer_id
			<< "): size=" << pkt.getSize() << std::endl;
	Send(&pkt);
}

/*
	Non-static send methods
*/

void Server::SendInventory(PlayerSAO *sao, bool incremental)
{
	RemotePlayer *player = sao->getPlayer();
	incremental &= player->protocol_version >= 38;
	UpdateCrafting(player);
	NetworkPacket pkt(TOCLIENT_INVENTORY, 0, sao->getPeerID());
	std::ostringstream os(std::ios::binary);
	sao->getInventory()->serialize(os, incremental);
	sao->getInventory()->setModified(false);
	player->setModified(true);
	const std::string &s = os.str();
	pkt.putRawString(s.c_str(), s.size());
	Send(&pkt);
}

void Server::SendChatMessage(session_t peer_id, const ChatMessage &message)
{
	NetworkPacket pkt(TOCLIENT_CHAT_MESSAGE, 0, peer_id);
	u8 version = 1;
	u8 type = message.type;
	pkt << version << type << std::wstring(L"") << message.message << (u64)message.timestamp;
	if (peer_id != PEER_ID_INEXISTENT) {
		RemotePlayer *player = m_env->getPlayer(peer_id);
		if (!player)
			return;
		Send(&pkt);
	} else {
		m_clients.sendToAll(&pkt);
	}
}

void Server::SendShowFormspecMessage(session_t peer_id, const std::string &formspec,
	const std::string &formname)
{
	NetworkPacket pkt(TOCLIENT_SHOW_FORMSPEC, 0, peer_id);
	if (formspec.empty()){
		const auto it = m_formspec_state_data.find(peer_id);
		if (it != m_formspec_state_data.end() && it->second == formname) {
			m_formspec_state_data.erase(peer_id);
		}
		pkt.putLongString("");
	} else {
		m_formspec_state_data[peer_id] = formname;
		pkt.putLongString(formspec);
	}
	pkt << formname;
	Send(&pkt);
}

void Server::SendSpawnParticle(session_t peer_id, u16 protocol_version,
				v3f pos, v3f velocity, v3f acceleration,
				float expirationtime, float size, bool collisiondetection,
				bool collision_removal, bool object_collision,
				bool vertical, const std::string &texture,
				const struct TileAnimationParams &animation, u8 glow)
{
	static thread_local const float radius =
			g_settings->getS16("max_block_send_distance") * MAP_BLOCKSIZE * BS;
	if (peer_id == PEER_ID_INEXISTENT) {
		std::vector<session_t> clients = m_clients.getClientIDs();
		for (const session_t client_id : clients) {
			RemotePlayer *player = m_env->getPlayer(client_id);
			if (!player)
				continue;
			PlayerSAO *sao = player->getPlayerSAO();
			if (!sao)
				continue;
			if (sao->getBasePosition().getDistanceFrom(pos * BS) > radius)
				continue;
			SendSpawnParticle(client_id, player->protocol_version,
					pos, velocity, acceleration,
					expirationtime, size, collisiondetection, collision_removal,
					object_collision, vertical, texture, animation, glow);
		}
		return;
	}
	NetworkPacket pkt(TOCLIENT_SPAWN_PARTICLE, 0, peer_id);
	pkt << pos << velocity << acceleration << expirationtime
			<< size << collisiondetection;
	pkt.putLongString(texture);
	pkt << vertical;
	pkt << collision_removal;
	std::ostringstream os(std::ios_base::binary);
	animation.serialize(os, protocol_version);
	pkt.putRawString(os.str());
	pkt << glow;
	pkt << object_collision;
	Send(&pkt);
}

void Server::SendAddParticleSpawner(session_t peer_id, u16 protocol_version,
	u16 amount, float spawntime, v3f minpos, v3f maxpos,
	v3f minvel, v3f maxvel, v3f minacc, v3f maxacc, float minexptime, float maxexptime,
	float minsize, float maxsize, bool collisiondetection, bool collision_removal,
	bool object_collision, u16 attached_id, bool vertical, const std::string &texture, u32 id,
	const struct TileAnimationParams &animation, u8 glow)
{
	if (peer_id == PEER_ID_INEXISTENT) {
		std::vector<session_t> clients = m_clients.getClientIDs();
		for (const session_t client_id : clients) {
			RemotePlayer *player = m_env->getPlayer(client_id);
			if (!player)
				continue;
			SendAddParticleSpawner(client_id, player->protocol_version,
					amount, spawntime, minpos, maxpos,
					minvel, maxvel, minacc, maxacc, minexptime, maxexptime,
					minsize, maxsize, collisiondetection, collision_removal,
					object_collision, attached_id, vertical, texture, id,
					animation, glow);
		}
		return;
	}
	NetworkPacket pkt(TOCLIENT_ADD_PARTICLESPAWNER, 0, peer_id);
	pkt << amount << spawntime << minpos << maxpos << minvel << maxvel
			<< minacc << maxacc << minexptime << maxexptime << minsize
			<< maxsize << collisiondetection;
	pkt.putLongString(texture);
	pkt << id << vertical;
	pkt << collision_removal;
	pkt << attached_id;
	std::ostringstream os(std::ios_base::binary);
	animation.serialize(os, protocol_version);
	pkt.putRawString(os.str());
	pkt << glow;
	pkt << object_collision;
	Send(&pkt);
}

void Server::SendDeleteParticleSpawner(session_t peer_id, u32 id)
{
	NetworkPacket pkt(TOCLIENT_DELETE_PARTICLESPAWNER, 4, peer_id);
	pkt << id;
	if (peer_id != PEER_ID_INEXISTENT)
		Send(&pkt);
	else
		m_clients.sendToAll(&pkt);
}

void Server::SendHUDAdd(session_t peer_id, u32 id, HudElement *form)
{
	NetworkPacket pkt(TOCLIENT_HUDADD, 0 , peer_id);
	pkt << id << (u8) form->type << form->pos << form->name << form->scale
			<< form->text << form->number << form->item << form->dir
			<< form->align << form->offset << form->world_pos << form->size
			<< form->z_index;
	Send(&pkt);
}

void Server::SendHUDRemove(session_t peer_id, u32 id)
{
	NetworkPacket pkt(TOCLIENT_HUDRM, 4, peer_id);
	pkt << id;
	Send(&pkt);
}

void Server::SendHUDChange(session_t peer_id, u32 id, HudElementStat stat, void *value)
{
	NetworkPacket pkt(TOCLIENT_HUDCHANGE, 0, peer_id);
	pkt << id << (u8) stat;
	switch (stat) {
		case HUD_STAT_POS:
		case HUD_STAT_SCALE:
		case HUD_STAT_ALIGN:
		case HUD_STAT_OFFSET:
			pkt << *(v2f *) value;
			break;
		case HUD_STAT_NAME:
		case HUD_STAT_TEXT:
			pkt << *(std::string *) value;
			break;
		case HUD_STAT_WORLD_POS:
			pkt << *(v3f *) value;
			break;
		case HUD_STAT_SIZE:
			pkt << *(v2s32 *) value;
			break;
		case HUD_STAT_NUMBER:
		case HUD_STAT_ITEM:
		case HUD_STAT_DIR:
		default:
			pkt << *(u32 *) value;
			break;
	}
	Send(&pkt);
}

void Server::SendHUDSetFlags(session_t peer_id, u32 flags, u32 mask)
{
	NetworkPacket pkt(TOCLIENT_HUD_SET_FLAGS, 4 + 4, peer_id);
	flags &= ~(HUD_FLAG_HEALTHBAR_VISIBLE | HUD_FLAG_BREATHBAR_VISIBLE);
	pkt << flags << mask;
	Send(&pkt);
}

void Server::SendHUDSetParam(session_t peer_id, u16 param, const std::string &value)
{
	NetworkPacket pkt(TOCLIENT_HUD_SET_PARAM, 0, peer_id);
	pkt << param << value;
	Send(&pkt);
}

void Server::SendSetSky(session_t peer_id, const SkyboxParams &params)
{
	NetworkPacket pkt(TOCLIENT_SET_SKY, 0, peer_id);
	if (m_clients.getProtocolVersion(peer_id) < 39) {
		pkt << params.bgcolor << params.type << (u16) params.textures.size();
		for (const std::string& texture : params.textures)
			pkt << texture;
		pkt << params.clouds;
	} else {
		pkt << params.bgcolor << params.type
		<< params.clouds << params.sun_tint
		<< params.moon_tint << params.tint_type;
		if (params.type == "skybox") {
			pkt << (u16) params.textures.size();
			for (const std::string &texture : params.textures)
				pkt << texture;
		} else if (params.type == "regular") {
			pkt << params.sky_color.day_sky << params.sky_color.day_horizon
				<< params.sky_color.dawn_sky << params.sky_color.dawn_horizon
				<< params.sky_color.night_sky << params.sky_color.night_horizon
				<< params.sky_color.indoors;
		}
	}
	Send(&pkt);
}

void Server::SendSetSun(session_t peer_id, const SunParams &params)
{
	NetworkPacket pkt(TOCLIENT_SET_SUN, 0, peer_id);
	pkt << params.visible << params.texture
		<< params.tonemap << params.sunrise
		<< params.sunrise_visible << params.scale;
	Send(&pkt);
}

void Server::SendSetMoon(session_t peer_id, const MoonParams &params)
{
	NetworkPacket pkt(TOCLIENT_SET_MOON, 0, peer_id);
	pkt << params.visible << params.texture
		<< params.tonemap << params.scale;
	Send(&pkt);
}

void Server::SendSetStars(session_t peer_id, const StarParams &params)
{
	NetworkPacket pkt(TOCLIENT_SET_STARS, 0, peer_id);
	pkt << params.visible << params.count
		<< params.starcolor << params.scale;
	Send(&pkt);
}

void Server::SendCloudParams(session_t peer_id, const CloudParams &params)
{
	NetworkPacket pkt(TOCLIENT_CLOUD_PARAMS, 0, peer_id);
	pkt << params.density << params.color_bright << params.color_ambient
			<< params.height << params.thickness << params.speed;
	Send(&pkt);
}

void Server::SendOverrideDayNightRatio(session_t peer_id, bool do_override,
		float ratio)
{
	NetworkPacket pkt(TOCLIENT_OVERRIDE_DAY_NIGHT_RATIO,
			1 + 2, peer_id);
	pkt << do_override << (u16) (ratio * 65535);
	Send(&pkt);
}

void Server::SendTimeOfDay(session_t peer_id, u16 time, f32 time_speed)
{
	NetworkPacket pkt(TOCLIENT_TIME_OF_DAY, 0, peer_id);
	pkt << time << time_speed;
	if (peer_id == PEER_ID_INEXISTENT) {
		m_clients.sendToAll(&pkt);
	}
	else {
		Send(&pkt);
	}
}

void Server::SendPlayerHP(session_t peer_id)
{
	PlayerSAO *playersao = getPlayerSAO(peer_id);
	assert(playersao);
	SendHP(peer_id, playersao->getHP());
	m_script->player_event(playersao,"health_changed");
	std::string str = gob_cmd_punched(playersao->getHP());
	ActiveObjectMessage aom(playersao->getId(), true, str);
	playersao->m_messages_out.push(aom);
}

void Server::SendPlayerBreath(PlayerSAO *sao)
{
	assert(sao);
	m_script->player_event(sao, "breath_changed");
	SendBreath(sao->getPeerID(), sao->getBreath());
}

void Server::SendMovePlayer(session_t peer_id)
{
	RemotePlayer *player = m_env->getPlayer(peer_id);
	assert(player);
	PlayerSAO *sao = player->getPlayerSAO();
	assert(sao);
	NetworkPacket pkt(TOCLIENT_MOVE_PLAYER, sizeof(v3f) + sizeof(f32) * 2, peer_id);
	pkt << sao->getBasePosition() << sao->getLookPitch() << sao->getRotation().Y;
	{
		v3f pos = sao->getBasePosition();
		verbosestream << "Server: Sending TOCLIENT_MOVE_PLAYER"
				<< " pos=(" << pos.X << "," << pos.Y << "," << pos.Z << ")"
				<< " pitch=" << sao->getLookPitch()
				<< " yaw=" << sao->getRotation().Y
				<< std::endl;
	}
	Send(&pkt);
}

void Server::SendPlayerFov(session_t peer_id)
{
	NetworkPacket pkt(TOCLIENT_FOV, 4 + 1, peer_id);
	PlayerFovSpec fov_spec = m_env->getPlayer(peer_id)->getFov();
	pkt << fov_spec.fov << fov_spec.is_multiplier;
	Send(&pkt);
}

void Server::SendLocalPlayerAnimations(session_t peer_id, v2s32 animation_frames[4],
		f32 animation_speed)
{
	NetworkPacket pkt(TOCLIENT_LOCAL_PLAYER_ANIMATIONS, 0, peer_id);
	pkt << animation_frames[0] << animation_frames[1] << animation_frames[2]
			<< animation_frames[3] << animation_speed;
	Send(&pkt);
}

void Server::SendEyeOffset(session_t peer_id, v3f first, v3f third)
{
	NetworkPacket pkt(TOCLIENT_EYE_OFFSET, 0, peer_id);
	pkt << first << third;
	Send(&pkt);
}

void Server::SendPlayerPrivileges(session_t peer_id)
{
	RemotePlayer *player = m_env->getPlayer(peer_id);
	assert(player);
	if(player->getPeerId() == PEER_ID_INEXISTENT)
		return;
	std::set<std::string> privs;
	m_script->getAuth(player->getName(), NULL, &privs);
	NetworkPacket pkt(TOCLIENT_PRIVILEGES, 0, peer_id);
	pkt << (u16) privs.size();
	for (const std::string &priv : privs) {
		pkt << priv;
	}
	Send(&pkt);
}

void Server::SendPlayerInventoryFormspec(session_t peer_id)
{
	RemotePlayer *player = m_env->getPlayer(peer_id);
	assert(player);
	if (player->getPeerId() == PEER_ID_INEXISTENT)
		return;
	NetworkPacket pkt(TOCLIENT_INVENTORY_FORMSPEC, 0, peer_id);
	pkt.putLongString(player->inventory_formspec);
	Send(&pkt);
}

void Server::SendPlayerFormspecPrepend(session_t peer_id)
{
	RemotePlayer *player = m_env->getPlayer(peer_id);
	assert(player);
	if (player->getPeerId() == PEER_ID_INEXISTENT)
		return;
	NetworkPacket pkt(TOCLIENT_FORMSPEC_PREPEND, 0, peer_id);
	pkt << player->formspec_prepend;
	Send(&pkt);
}

void Server::SendActiveObjectRemoveAdd(RemoteClient *client, PlayerSAO *playersao)
{
	static thread_local const s16 radius =
		g_settings->getS16("active_object_send_range_blocks") * MAP_BLOCKSIZE;
	static thread_local const bool is_transfer_limited =
		g_settings->exists("unlimited_player_transfer_distance") &&
		!g_settings->getBool("unlimited_player_transfer_distance");
	static thread_local const s16 player_transfer_dist =
		g_settings->getS16("player_transfer_distance") * MAP_BLOCKSIZE;
	s16 player_radius = player_transfer_dist == 0 && is_transfer_limited ?
		radius : player_transfer_dist;
	s16 my_radius = MYMIN(radius, playersao->getWantedRange() * MAP_BLOCKSIZE);
	if (my_radius <= 0)
		my_radius = radius;
	std::queue<u16> removed_objects, added_objects;
	m_env->getRemovedActiveObjects(playersao, my_radius, player_radius,
		client->m_known_objects, removed_objects);
	m_env->getAddedActiveObjects(playersao, my_radius, player_radius,
		client->m_known_objects, added_objects);
	int removed_count = removed_objects.size();
	int added_count   = added_objects.size();
	if (removed_objects.empty() && added_objects.empty())
		return;
	char buf[4];
	std::string data;
	writeU16((u8*)buf, removed_objects.size());
	data.append(buf, 2);
	while (!removed_objects.empty()) {
		u16 id = removed_objects.front();
		ServerActiveObject* obj = m_env->getActiveObject(id);
		writeU16((u8*)buf, id);
		data.append(buf, 2);
		client->m_known_objects.erase(id);
		if (obj && obj->m_known_by_count > 0)
			obj->m_known_by_count--;
		removed_objects.pop();
	}
	writeU16((u8*)buf, added_objects.size());
	data.append(buf, 2);
	while (!added_objects.empty()) {
		u16 id = added_objects.front();
		ServerActiveObject *obj = m_env->getActiveObject(id);
		added_objects.pop();
		if (!obj) {
			warningstream << FUNCTION_NAME << ": NULL object id="
				<< (int)id << std::endl;
			continue;
		}
		u8 type = obj->getSendType();
		writeU16((u8*)buf, id);
		data.append(buf, 2);
		writeU8((u8*)buf, type);
		data.append(buf, 1);
		data.append(serializeLongString(
			obj->getClientInitializationData(client->net_proto_version)));
		client->m_known_objects.insert(id);
		obj->m_known_by_count++;
	}
	NetworkPacket pkt(TOCLIENT_ACTIVE_OBJECT_REMOVE_ADD, data.size(), client->peer_id);
	pkt.putRawString(data.c_str(), data.size());
	Send(&pkt);
	verbosestream << "Server::SendActiveObjectRemoveAdd: "
		<< removed_count << " removed, " << added_count << " added, "
		<< "packet size is " << pkt.getSize() << std::endl;
}

void Server::SendActiveObjectMessages(session_t peer_id, const std::string &datas,
		bool reliable)
{
	NetworkPacket pkt(TOCLIENT_ACTIVE_OBJECT_MESSAGES,
			datas.size(), peer_id);
	pkt.putRawString(datas.c_str(), datas.size());
	m_clients.send(pkt.getPeerId(),
			reliable ? clientCommandFactoryTable[pkt.getCommand()].channel : 1,
			&pkt, reliable);
}

void Server::SendCSMRestrictionFlags(session_t peer_id)
{
	NetworkPacket pkt(TOCLIENT_CSM_RESTRICTION_FLAGS,
		sizeof(m_csm_restriction_flags) + sizeof(m_csm_restriction_noderange), peer_id);
	pkt << m_csm_restriction_flags << m_csm_restriction_noderange;
	Send(&pkt);
}

void Server::SendPlayerSpeed(session_t peer_id, const v3f &added_vel)
{
	NetworkPacket pkt(TOCLIENT_PLAYER_SPEED, 0, peer_id);
	pkt << added_vel;
	Send(&pkt);
}

inline s32 Server::nextSoundId()
{
	s32 ret = m_next_sound_id;
	if (m_next_sound_id == INT32_MAX)
		m_next_sound_id = 0;
	else
		m_next_sound_id++;
	return ret;
}

s32 Server::playSound(const SimpleSoundSpec &spec,
		const ServerSoundParams &params, bool ephemeral)
{
	bool pos_exists = false;
	v3f pos = params.getPos(m_env, &pos_exists);
	if(pos_exists != (params.type != ServerSoundParams::SSP_LOCAL))
		return -1;
	std::vector<session_t> dst_clients;
	if (!params.to_player.empty()) {
		RemotePlayer *player = m_env->getPlayer(params.to_player.c_str());
		if(!player){
			infostream<<"Server::playSound: Player \""<<params.to_player
					<<"\" not found"<<std::endl;
			return -1;
		}
		if (player->getPeerId() == PEER_ID_INEXISTENT) {
			infostream<<"Server::playSound: Player \""<<params.to_player
					<<"\" not connected"<<std::endl;
			return -1;
		}
		dst_clients.push_back(player->getPeerId());
	} else {
		std::vector<session_t> clients = m_clients.getClientIDs();
		for (const session_t client_id : clients) {
			RemotePlayer *player = m_env->getPlayer(client_id);
			if (!player)
				continue;
			if (!params.exclude_player.empty() &&
					params.exclude_player == player->getName())
				continue;
			PlayerSAO *sao = player->getPlayerSAO();
			if (!sao)
				continue;
			if (pos_exists) {
				if(sao->getBasePosition().getDistanceFrom(pos) >
						params.max_hear_distance)
					continue;
			}
			dst_clients.push_back(client_id);
		}
	}
	if(dst_clients.empty())
		return -1;
	s32 id;
	ServerPlayingSound *psound = nullptr;
	if (ephemeral) {
		id = -1;
	} else {
		id = nextSoundId();
		m_playing_sounds[id] = ServerPlayingSound();
		psound = &m_playing_sounds[id];
		psound->params = params;
		psound->spec = spec;
	}
	float gain = params.gain * spec.gain;
	NetworkPacket pkt(TOCLIENT_PLAY_SOUND, 0);
	pkt << id << spec.name << gain
			<< (u8) params.type << pos << params.object
			<< params.loop << params.fade << params.pitch
			<< ephemeral;
	bool as_reliable = !ephemeral;
	for (const u16 dst_client : dst_clients) {
		if (psound)
			psound->clients.insert(dst_client);
		m_clients.send(dst_client, 0, &pkt, as_reliable);
	}
	return id;
}

void Server::stopSound(s32 handle)
{
	std::unordered_map<s32, ServerPlayingSound>::iterator i =
		m_playing_sounds.find(handle);
	if (i == m_playing_sounds.end())
		return;
	ServerPlayingSound &psound = i->second;
	NetworkPacket pkt(TOCLIENT_STOP_SOUND, 4);
	pkt << handle;
	for (std::unordered_set<session_t>::const_iterator si = psound.clients.begin();
			si != psound.clients.end(); ++si) {
		m_clients.send(*si, 0, &pkt, true);
	}
	m_playing_sounds.erase(i);
}

void Server::fadeSound(s32 handle, float step, float gain)
{
	std::unordered_map<s32, ServerPlayingSound>::iterator i =
		m_playing_sounds.find(handle);
	if (i == m_playing_sounds.end())
		return;
	ServerPlayingSound &psound = i->second;
	psound.params.gain = gain;
	NetworkPacket pkt(TOCLIENT_FADE_SOUND, 4);
	pkt << handle << step << gain;
	bool play_sound = gain > 0;
	ServerPlayingSound compat_psound = psound;
	compat_psound.clients.clear();
	NetworkPacket compat_pkt(TOCLIENT_STOP_SOUND, 4);
	compat_pkt << handle;
	for (std::unordered_set<u16>::iterator it = psound.clients.begin();
			it != psound.clients.end();) {
		if (m_clients.getProtocolVersion(*it) >= 32) {
			m_clients.send(*it, 0, &pkt, true);
			++it;
		} else {
			compat_psound.clients.insert(*it);
			m_clients.send(*it, 0, &compat_pkt, true);
			psound.clients.erase(it++);
		}
	}
	if (!play_sound || psound.clients.empty())
		m_playing_sounds.erase(i);
	if (play_sound && !compat_psound.clients.empty()) {
		playSound(compat_psound.spec, compat_psound.params);
	}
}

void Server::sendRemoveNode(v3s16 p, std::unordered_set<u16> *far_players,
		float far_d_nodes)
{
	float maxd = far_d_nodes * BS;
	v3f p_f = intToFloat(p, BS);
	v3s16 block_pos = getNodeBlockPos(p);
	NetworkPacket pkt(TOCLIENT_REMOVENODE, 6);
	pkt << p;
	std::vector<session_t> clients = m_clients.getClientIDs();
	m_clients.lock();
	for (session_t client_id : clients) {
		RemoteClient *client = m_clients.lockedGetClientNoEx(client_id);
		if (!client)
			continue;
		RemotePlayer *player = m_env->getPlayer(client_id);
		PlayerSAO *sao = player ? player->getPlayerSAO() : nullptr;
		if (!client->isBlockSent(block_pos) || (sao &&
				sao->getBasePosition().getDistanceFrom(p_f) > maxd)) {
			if (far_players)
				far_players->emplace(client_id);
			else
				client->SetBlockNotSent(block_pos);
			continue;
		}
		m_clients.send(client_id, 0, &pkt, true);
	}
	m_clients.unlock();
}

void Server::sendAddNode(v3s16 p, MapNode n, std::unordered_set<u16> *far_players,
		float far_d_nodes, bool remove_metadata)
{
	float maxd = far_d_nodes * BS;
	v3f p_f = intToFloat(p, BS);
	v3s16 block_pos = getNodeBlockPos(p);
	NetworkPacket pkt(TOCLIENT_ADDNODE, 6 + 2 + 1 + 1 + 1);
	pkt << p << n.param0 << n.param1 << n.param2
			<< (u8) (remove_metadata ? 0 : 1);
	std::vector<session_t> clients = m_clients.getClientIDs();
	m_clients.lock();
	for (session_t client_id : clients) {
		RemoteClient *client = m_clients.lockedGetClientNoEx(client_id);
		if (!client)
			continue;
		RemotePlayer *player = m_env->getPlayer(client_id);
		PlayerSAO *sao = player ? player->getPlayerSAO() : nullptr;
		if (!client->isBlockSent(block_pos) || (sao &&
				sao->getBasePosition().getDistanceFrom(p_f) > maxd)) {
			if (far_players)
				far_players->emplace(client_id);
			else
				client->SetBlockNotSent(block_pos);
			continue;
		}
		m_clients.send(client_id, 0, &pkt, true);
	}
	m_clients.unlock();
}

void Server::sendMetadataChanged(const std::list<v3s16> &meta_updates, float far_d_nodes)
{
	float maxd = far_d_nodes * BS;
	NodeMetadataList meta_updates_list(false);
	std::vector<session_t> clients = m_clients.getClientIDs();
	m_clients.lock();
	for (session_t i : clients) {
		RemoteClient *client = m_clients.lockedGetClientNoEx(i);
		if (!client)
			continue;
		ServerActiveObject *player = m_env->getActiveObject(i);
		v3f player_pos = player ? player->getBasePosition() : v3f();
		for (const v3s16 &pos : meta_updates) {
			NodeMetadata *meta = m_env->getMap().getNodeMetadata(pos);
			if (!meta)
				continue;
			v3s16 block_pos = getNodeBlockPos(pos);
			if (!client->isBlockSent(block_pos) || (player &&
					player_pos.getDistanceFrom(intToFloat(pos, BS)) > maxd)) {
				client->SetBlockNotSent(block_pos);
				continue;
			}
			meta_updates_list.set(pos, meta);
		}
		if (meta_updates_list.size() == 0)
			continue;
		std::ostringstream os(std::ios::binary);
		meta_updates_list.serialize(os, client->net_proto_version, false, true);
		std::ostringstream oss(std::ios::binary);
		compressZlib(os.str(), oss);
		NetworkPacket pkt(TOCLIENT_NODEMETA_CHANGED, 0);
		pkt.putLongString(oss.str());
		m_clients.send(i, 0, &pkt, true);
		meta_updates_list.clear();
	}
	m_clients.unlock();
}

void Server::SendBlockNoLock(session_t peer_id, MapBlock *block, u8 ver,
		u16 net_proto_version)
{
	std::ostringstream os(std::ios_base::binary);
	block->serialize(os, ver, false);
	block->serializeNetworkSpecific(os);
	std::string s = os.str();
	NetworkPacket pkt(TOCLIENT_BLOCKDATA, 2 + 2 + 2 + 2 + s.size(), peer_id);
	pkt << block->getPos();
	pkt.putRawString(s.c_str(), s.size());
	Send(&pkt);
}

void Server::SendBlocks(float dtime)
{
	MutexAutoLock envlock(m_env_mutex);
	std::vector<PrioritySortedBlockTransfer> queue;
	u32 total_sending = 0;
	{
		ScopeProfiler sp2(g_profiler, "Server::SendBlocks(): Collect list");
		std::vector<session_t> clients = m_clients.getClientIDs();
		m_clients.lock();
		for (const session_t client_id : clients) {
			RemoteClient *client = m_clients.lockedGetClientNoEx(client_id, CS_Active);
			if (!client)
				continue;
			total_sending += client->getSendingCount();
			client->GetNextBlocks(m_env,m_emerge, dtime, queue);
		}
		m_clients.unlock();
	}
	std::sort(queue.begin(), queue.end());
	m_clients.lock();
	u32 max_blocks_to_send = (m_env->getPlayerCount() + g_settings->getU32("max_users")) *
		g_settings->getU32("max_simultaneous_block_sends_per_client") / 4 + 1;
	ScopeProfiler sp(g_profiler, "Server::SendBlocks(): Send to clients");
	Map &map = m_env->getMap();
	for (const PrioritySortedBlockTransfer &block_to_send : queue) {
		if (total_sending >= max_blocks_to_send)
			break;
		MapBlock *block = map.getBlockNoCreateNoEx(block_to_send.pos);
		if (!block)
			continue;
		RemoteClient *client = m_clients.lockedGetClientNoEx(block_to_send.peer_id,
				CS_Active);
		if (!client)
			continue;
		SendBlockNoLock(block_to_send.peer_id, block, client->serialization_version,
				client->net_proto_version);
		client->SentBlock(block_to_send.pos);
		total_sending++;
	}
	m_clients.unlock();
}

bool Server::SendBlock(session_t peer_id, const v3s16 &blockpos)
{
	MapBlock *block = m_env->getMap().getBlockNoCreateNoEx(blockpos);
	if (!block)
		return false;
	m_clients.lock();
	RemoteClient *client = m_clients.lockedGetClientNoEx(peer_id, CS_Active);
	if (!client || client->isBlockSent(blockpos)) {
		m_clients.unlock();
		return false;
	}
	SendBlockNoLock(peer_id, block, client->serialization_version,
			client->net_proto_version);
	m_clients.unlock();
	return true;
}

void Server::fillMediaCache()
{
	infostream<<"Server: Calculating media file checksums"<<std::endl;
	std::vector<std::string> paths;
	m_modmgr->getModsMediaPaths(paths);
	fs::GetRecursiveDirs(paths, m_gamespec.path + DIR_DELIM + "textures");
	fs::GetRecursiveDirs(paths, porting::path_user + DIR_DELIM + "textures" + DIR_DELIM + "server");
	for (const std::string &mediapath : paths) {
		std::vector<fs::DirListNode> dirlist = fs::GetDirListing(mediapath);
		for (const fs::DirListNode &dln : dirlist) {
			if (dln.dir)
				continue;
			std::string filename = dln.name;
			if (!string_allowed(filename, TEXTURENAME_ALLOWED_CHARS)) {
				infostream<<"Server: ignoring illegal file name: \""
						<< filename << "\"" << std::endl;
				continue;
			}
			const char *supported_ext[] = {
				".png", ".jpg", ".bmp", ".tga",
				".pcx", ".ppm", ".psd", ".wal", ".rgb",
				".ogg",
				".x", ".b3d", ".md2", ".obj",
				".tr",
				NULL
			};
			if (removeStringEnd(filename, supported_ext).empty()){
				infostream << "Server: ignoring unsupported file extension: \""
						<< filename << "\"" << std::endl;
				continue;
			}
			std::string filepath;
			filepath.append(mediapath).append(DIR_DELIM).append(filename);
			std::ifstream fis(filepath.c_str(), std::ios_base::binary);
			if (!fis.good()) {
				errorstream << "Server::fillMediaCache(): Could not open \""
						<< filename << "\" for reading" << std::endl;
				continue;
			}
			std::ostringstream tmp_os(std::ios_base::binary);
			bool bad = false;
			for(;;) {
				char buf[1024];
				fis.read(buf, 1024);
				std::streamsize len = fis.gcount();
				tmp_os.write(buf, len);
				if (fis.eof())
					break;
				if (!fis.good()) {
					bad = true;
					break;
				}
			}
			if(bad) {
				errorstream<<"Server::fillMediaCache(): Failed to read \""
						<< filename << "\"" << std::endl;
				continue;
			}
			if(tmp_os.str().length() == 0) {
				errorstream << "Server::fillMediaCache(): Empty file \""
						<< filepath << "\"" << std::endl;
				continue;
			}
			SHA1 sha1;
			sha1.addBytes(tmp_os.str().c_str(), tmp_os.str().length());
			unsigned char *digest = sha1.getDigest();
			std::string sha1_base64 = base64_encode(digest, 20);
			std::string sha1_hex = hex_encode((char*)digest, 20);
			free(digest);
			m_media[filename] = MediaInfo(filepath, sha1_base64);
			verbosestream << "Server: " << sha1_hex << " is " << filename
					<< std::endl;
		}
	}
}

void Server::sendMediaAnnouncement(session_t peer_id, const std::string &lang_code)
{
	verbosestream << "Server: Announcing files to id(" << peer_id << ")"
		<< std::endl;
	NetworkPacket pkt(TOCLIENT_ANNOUNCE_MEDIA, 0, peer_id);
	u16 media_sent = 0;
	std::string lang_suffix;
	lang_suffix.append(".").append(lang_code).append(".tr");
	for (const auto &i : m_media) {
		if (str_ends_with(i.first, ".tr") && !str_ends_with(i.first, lang_suffix))
			continue;
		media_sent++;
	}
	pkt << media_sent;
	for (const auto &i : m_media) {
		if (str_ends_with(i.first, ".tr") && !str_ends_with(i.first, lang_suffix))
			continue;
		pkt << i.first << i.second.sha1_digest;
	}
	pkt << g_settings->get("remote_media");
	Send(&pkt);
}

struct SendableMedia
{
	std::string name;
	std::string path;
	std::string data;
	SendableMedia(const std::string &name_="", const std::string &path_="",
	              const std::string &data_=""):
		name(name_),
		path(path_),
		data(data_)
	{}
};

void Server::sendRequestedMedia(session_t peer_id,
		const std::vector<std::string> &tosend)
{
	verbosestream<<"Server::sendRequestedMedia(): "
			<<"Sending files to client"<<std::endl;
	u32 bytes_per_bunch = 5000;
	std::vector< std::vector<SendableMedia> > file_bunches;
	file_bunches.emplace_back();
	u32 file_size_bunch_total = 0;
	for (const std::string &name : tosend) {
		if (m_media.find(name) == m_media.end()) {
			errorstream<<"Server::sendRequestedMedia(): Client asked for "
					<<"unknown file \""<<(name)<<"\""<<std::endl;
			continue;
		}
		std::string tpath = m_media[name].path;
		std::ifstream fis(tpath.c_str(), std::ios_base::binary);
		if(!fis.good()){
			errorstream<<"Server::sendRequestedMedia(): Could not open \""
					<<tpath<<"\" for reading"<<std::endl;
			continue;
		}
		std::ostringstream tmp_os(std::ios_base::binary);
		bool bad = false;
		for(;;) {
			char buf[1024];
			fis.read(buf, 1024);
			std::streamsize len = fis.gcount();
			tmp_os.write(buf, len);
			file_size_bunch_total += len;
			if(fis.eof())
				break;
			if(!fis.good()) {
				bad = true;
				break;
			}
		}
		if (bad) {
			errorstream<<"Server::sendRequestedMedia(): Failed to read \""
					<<name<<"\""<<std::endl;
			continue;
		}
		file_bunches[file_bunches.size()-1].emplace_back(name, tpath, tmp_os.str());
		if(file_size_bunch_total >= bytes_per_bunch) {
			file_bunches.emplace_back();
			file_size_bunch_total = 0;
		}
	}
	u16 num_bunches = file_bunches.size();
	for (u16 i = 0; i < num_bunches; i++) {
		NetworkPacket pkt(TOCLIENT_MEDIA, 4 + 0, peer_id);
		pkt << num_bunches << i << (u32) file_bunches[i].size();
		for (const SendableMedia &j : file_bunches[i]) {
			pkt << j.name;
			pkt.putLongString(j.data);
		}
		verbosestream << "Server::sendRequestedMedia(): bunch "
				<< i << "/" << num_bunches
				<< " files=" << file_bunches[i].size()
				<< " size="  << pkt.getSize() << std::endl;
		Send(&pkt);
	}
}

void Server::sendDetachedInventory(const std::string &name, session_t peer_id)
{
	const auto &inv_it = m_detached_inventories.find(name);
	const auto &player_it = m_detached_inventories_player.find(name);
	if (player_it == m_detached_inventories_player.end() ||
			player_it->second.empty()) {
	} else {
		if (!m_env)
			return;
		RemotePlayer *p = m_env->getPlayer(player_it->second.c_str());
		if (!p)
			return;
		if (peer_id != PEER_ID_INEXISTENT && peer_id != p->getPeerId())
			return;
		peer_id = p->getPeerId();
	}
	NetworkPacket pkt(TOCLIENT_DETACHED_INVENTORY, 0, peer_id);
	pkt << name;
	if (inv_it == m_detached_inventories.end()) {
		pkt << false;
	} else {
		pkt << true;
		std::ostringstream os(std::ios_base::binary);
		inv_it->second->serialize(os);
		inv_it->second->setModified(false);
		const std::string &os_str = os.str();
		pkt << static_cast<u16>(os_str.size());
		pkt.putRawString(os_str);
	}
	if (peer_id == PEER_ID_INEXISTENT)
		m_clients.sendToAll(&pkt);
	else
		Send(&pkt);
}

void Server::sendDetachedInventories(session_t peer_id, bool incremental)
{
	for (const auto &detached_inventory : m_detached_inventories) {
		const std::string &name = detached_inventory.first;
		if (incremental) {
			Inventory *inv = detached_inventory.second;
			if (!inv || !inv->checkModified())
				continue;
		}
		sendDetachedInventory(name, peer_id);
	}
}

/*
	Something random
*/

void Server::DiePlayer(session_t peer_id, const PlayerHPChangeReason &reason)
{
	PlayerSAO *playersao = getPlayerSAO(peer_id);
	assert(playersao);
	infostream << "Server::DiePlayer(): Player "
			<< playersao->getPlayer()->getName()
			<< " dies" << std::endl;
	playersao->setHP(0, reason);
	playersao->clearParentAttachment();
	m_script->on_dieplayer(playersao, reason);
	SendPlayerHP(peer_id);
	SendDeathscreen(peer_id, false, v3f(0,0,0));
}

void Server::RespawnPlayer(session_t peer_id)
{
	PlayerSAO *playersao = getPlayerSAO(peer_id);
	assert(playersao);
	infostream << "Server::RespawnPlayer(): Player "
			<< playersao->getPlayer()->getName()
			<< " respawns" << std::endl;
	playersao->setHP(playersao->accessObjectProperties()->hp_max,
			PlayerHPChangeReason(PlayerHPChangeReason::RESPAWN));
	playersao->setBreath(playersao->accessObjectProperties()->breath_max);
	bool repositioned = m_script->on_respawnplayer(playersao);
	if (!repositioned) {
		playersao->setPos(findSpawnPos());
	}
	SendPlayerHP(peer_id);
}

void Server::DenySudoAccess(session_t peer_id)
{
	NetworkPacket pkt(TOCLIENT_DENY_SUDO_MODE, 0, peer_id);
	Send(&pkt);
}

void Server::DenyAccessVerCompliant(session_t peer_id, u16 proto_ver, AccessDeniedCode reason,
		const std::string &str_reason, bool reconnect)
{
	SendAccessDenied(peer_id, reason, str_reason, reconnect);
	m_clients.event(peer_id, CSE_SetDenied);
	DisconnectPeer(peer_id);
}

void Server::DenyAccess(session_t peer_id, AccessDeniedCode reason,
		const std::string &custom_reason)
{
	SendAccessDenied(peer_id, reason, custom_reason);
	m_clients.event(peer_id, CSE_SetDenied);
	DisconnectPeer(peer_id);
}

void Server::DenyAccess_Legacy(session_t peer_id, const std::wstring &reason)
{
	SendAccessDenied_Legacy(peer_id, reason);
	m_clients.event(peer_id, CSE_SetDenied);
	DisconnectPeer(peer_id);
}

void Server::DisconnectPeer(session_t peer_id)
{
	m_modchannel_mgr->leaveAllChannels(peer_id);
	m_con->DisconnectPeer(peer_id);
}

void Server::acceptAuth(session_t peer_id, bool forSudoMode)
{
	if (!forSudoMode) {
		RemoteClient* client = getClient(peer_id, CS_Invalid);
		NetworkPacket resp_pkt(TOCLIENT_AUTH_ACCEPT, 1 + 6 + 8 + 4, peer_id);
		u32 sudo_auth_mechs = client->allowed_auth_mechs;
		client->allowed_sudo_mechs = sudo_auth_mechs;
		resp_pkt << v3f(0,0,0) << (u64) m_env->getServerMap().getSeed()
				<< g_settings->getFloat("dedicated_server_step")
				<< sudo_auth_mechs;
		Send(&resp_pkt);
		m_clients.event(peer_id, CSE_AuthAccept);
	} else {
		NetworkPacket resp_pkt(TOCLIENT_ACCEPT_SUDO_MODE, 1 + 6 + 8 + 4, peer_id);
		u32 sudo_auth_mechs = AUTH_MECHANISM_FIRST_SRP;
		resp_pkt << sudo_auth_mechs;
		Send(&resp_pkt);
		m_clients.event(peer_id, CSE_SudoSuccess);
	}
}

void Server::DeleteClient(session_t peer_id, ClientDeletionReason reason)
{
	std::wstring message;
	{
		for (std::unordered_map<s32, ServerPlayingSound>::iterator
				 i = m_playing_sounds.begin(); i != m_playing_sounds.end();) {
			ServerPlayingSound &psound = i->second;
			psound.clients.erase(peer_id);
			if (psound.clients.empty())
				m_playing_sounds.erase(i++);
			else
				++i;
		}
		m_formspec_state_data.erase(peer_id);
		RemotePlayer *player = m_env->getPlayer(peer_id);
		if (player) {
			PlayerSAO *playersao = player->getPlayerSAO();
			assert(playersao);
			playersao->clearChildAttachments();
			playersao->clearParentAttachment();
			const std::string &player_name = player->getName();
			NetworkPacket notice(TOCLIENT_UPDATE_PLAYER_LIST, 0, PEER_ID_INEXISTENT);
			notice << (u8) PLAYER_LIST_REMOVE  << (u16) 1 << player_name;
			m_clients.sendToAll(&notice);
			m_script->on_leaveplayer(playersao, reason == CDR_TIMEOUT);
			playersao->disconnected();
		}
		{
			if (player && reason != CDR_DENY) {
				std::ostringstream os(std::ios_base::binary);
				std::vector<session_t> clients = m_clients.getClientIDs();
				for (const session_t client_id : clients) {
					RemotePlayer *player = m_env->getPlayer(client_id);
					if (!player)
						continue;
					os << player->getName() << " ";
				}
				std::string name = player->getName();
				actionstream << name << " "
						<< (reason == CDR_TIMEOUT ? "times out." : "leaves game.")
						<< " List of players: " << os.str() << std::endl;
				if (m_admin_chat)
					m_admin_chat->outgoing_queue.push_back(
						new ChatEventNick(CET_NICK_REMOVE, name));
			}
		}
		{
			MutexAutoLock env_lock(m_env_mutex);
			m_clients.DeleteClient(peer_id);
		}
	}
	if (!message.empty()) {
		SendChatMessage(PEER_ID_INEXISTENT,
				ChatMessage(CHATMESSAGE_TYPE_ANNOUNCE, message));
	}
}

void Server::UpdateCrafting(RemotePlayer *player)
{
	InventoryList *clist = player->inventory.getList("craft");
	if (!clist || clist->getSize() == 0)
		return;
	if (!clist->checkModified()) {
		verbosestream << "Skip Server::UpdateCrafting(): list unmodified" << std::endl;
		return;
	}
	ItemStack preview;
	InventoryLocation loc;
	loc.setPlayer(player->getName());
	std::vector<ItemStack> output_replacements;
	getCraftingResult(&player->inventory, preview, output_replacements, false, this);
	m_env->getScriptIface()->item_CraftPredict(preview, player->getPlayerSAO(),
			clist, loc);
	InventoryList *plist = player->inventory.getList("craftpreview");
	if (plist && plist->getSize() >= 1) {
		plist->changeItem(0, preview);
	}
}

void Server::handleChatInterfaceEvent(ChatEvent *evt)
{
	if (evt->type == CET_NICK_ADD) {
		m_admin_nick = ((ChatEventNick *)evt)->nick;
		if (!m_script->getAuth(m_admin_nick, NULL, NULL)) {
			errorstream << "You haven't set up an account." << std::endl
				<< "Please log in using the client as '"
				<< m_admin_nick << "' with a secure password." << std::endl
				<< "Until then, you can't execute admin tasks via the console," << std::endl
				<< "and everybody can claim the user account instead of you," << std::endl
				<< "giving them full control over this server." << std::endl;
		}
	} else {
		assert(evt->type == CET_CHAT);
		handleAdminChat((ChatEventChat *)evt);
	}
}

std::wstring Server::handleChat(const std::string &name, const std::wstring &wname,
	std::wstring wmessage, bool check_shout_priv, RemotePlayer *player)
{
	RollbackScopeActor rollback_scope(m_rollback,
			std::string("player:") + name);
	if (g_settings->getBool("strip_color_codes"))
		wmessage = unescape_enriched(wmessage);
	if (player) {
		switch (player->canSendChatMessage()) {
		case RPLAYER_CHATRESULT_FLOODING: {
			std::wstringstream ws;
			ws << L"You cannot send more messages. You are limited to "
					<< g_settings->getFloat("chat_message_limit_per_10sec")
					<< L" messages per 10 seconds.";
			return ws.str();
		}
		case RPLAYER_CHATRESULT_KICK:
			DenyAccess_Legacy(player->getPeerId(),
					L"You have been kicked due to message flooding.");
			return L"";
		case RPLAYER_CHATRESULT_OK:
			break;
		default:
			FATAL_ERROR("Unhandled chat filtering result found.");
		}
	}
	if (m_max_chatmessage_length > 0
			&& wmessage.length() > m_max_chatmessage_length) {
		return L"Your message exceed the maximum chat message limit set on the server. "
				L"It was refused. Send a shorter message";
	}
	auto message = trim(wide_to_utf8(wmessage));
	if (message.find_first_of("\n\r") != std::wstring::npos) {
		return L"New lines are not permitted in chat messages";
	}
	if (m_script->on_chat_message(name, message))
		return L"";
	std::wstring line;
	bool broadcast_line = true;
	if (check_shout_priv && !checkPriv(name, "shout")) {
		line += L"-!- You don't have permission to shout.";
		broadcast_line = false;
	} else {
		line += narrow_to_wide(m_script->formatChatMessage(name,
				wide_to_narrow(wmessage)));
	}
	if (!broadcast_line)
		return line;
	actionstream << "CHAT: " << wide_to_narrow(unescape_enriched(line)) << std::endl;
	std::vector<session_t> clients = m_clients.getClientIDs();
	session_t peer_id_to_avoid_sending =
		(player ? player->getPeerId() : PEER_ID_INEXISTENT);
	if (player && player->protocol_version >= 29)
		peer_id_to_avoid_sending = PEER_ID_INEXISTENT;
	for (u16 cid : clients) {
		if (cid != peer_id_to_avoid_sending)
			SendChatMessage(cid, ChatMessage(line));
	}
	return L"";
}

void Server::handleAdminChat(const ChatEventChat *evt)
{
	std::string name = evt->nick;
	std::wstring wname = utf8_to_wide(name);
	std::wstring wmessage = evt->evt_msg;
	std::wstring answer = handleChat(name, wname, wmessage);
	if (!answer.empty()) {
		m_admin_chat->outgoing_queue.push_back(new ChatEventChat("", answer));
	}
}

RemoteClient *Server::getClient(session_t peer_id, ClientState state_min)
{
	RemoteClient *client = getClientNoEx(peer_id,state_min);
	if(!client)
		throw ClientNotFoundException("Client not found");
	return client;
}

RemoteClient *Server::getClientNoEx(session_t peer_id, ClientState state_min)
{
	return m_clients.getClientNoEx(peer_id, state_min);
}

std::string Server::getPlayerName(session_t peer_id)
{
	RemotePlayer *player = m_env->getPlayer(peer_id);
	if (!player)
		return "[id="+itos(peer_id)+"]";
	return player->getName();
}

PlayerSAO *Server::getPlayerSAO(session_t peer_id)
{
	RemotePlayer *player = m_env->getPlayer(peer_id);
	if (!player)
		return NULL;
	return player->getPlayerSAO();
}

std::wstring Server::getStatusString()
{
	std::wostringstream os(std::ios_base::binary);
	os << L"# Server: ";
	os << L"version=" << narrow_to_wide(g_version_string);
	os << L", uptime=" << m_uptime.get();
	os << L", max_lag=" << (m_env ? m_env->getMaxLagEstimate() : 0);
	bool first = true;
	os << L", clients={";
	if (m_env) {
		std::vector<session_t> clients = m_clients.getClientIDs();
		for (session_t client_id : clients) {
			RemotePlayer *player = m_env->getPlayer(client_id);
			std::wstring name = L"unknown";
			if (player)
				name = narrow_to_wide(player->getName());
			if (!first)
				os << L", ";
			else
				first = false;
			os << name;
		}
	}
	os << L"}";
	if (m_env && !((ServerMap*)(&m_env->getMap()))->isSavingEnabled())
		os << std::endl << L"# Server: " << " WARNING: Map saving is disabled.";
	if (!g_settings->get("motd").empty())
		os << std::endl << L"# Server: " << narrow_to_wide(g_settings->get("motd"));
	return os.str();
}

std::set<std::string> Server::getPlayerEffectivePrivs(const std::string &name)
{
	std::set<std::string> privs;
	m_script->getAuth(name, NULL, &privs);
	return privs;
}

bool Server::checkPriv(const std::string &name, const std::string &priv)
{
	std::set<std::string> privs = getPlayerEffectivePrivs(name);
	return (privs.count(priv) != 0);
}

void Server::reportPrivsModified(const std::string &name)
{
	if (name.empty()) {
		std::vector<session_t> clients = m_clients.getClientIDs();
		for (const session_t client_id : clients) {
			RemotePlayer *player = m_env->getPlayer(client_id);
			reportPrivsModified(player->getName());
		}
	} else {
		RemotePlayer *player = m_env->getPlayer(name.c_str());
		if (!player)
			return;
		SendPlayerPrivileges(player->getPeerId());
		PlayerSAO *sao = player->getPlayerSAO();
		if(!sao)
			return;
		sao->updatePrivileges(
				getPlayerEffectivePrivs(name),
				isSingleplayer());
	}
}

void Server::reportInventoryFormspecModified(const std::string &name)
{
	RemotePlayer *player = m_env->getPlayer(name.c_str());
	if (!player)
		return;
	SendPlayerInventoryFormspec(player->getPeerId());
}

void Server::reportFormspecPrependModified(const std::string &name)
{
	RemotePlayer *player = m_env->getPlayer(name.c_str());
	if (!player)
		return;
	SendPlayerFormspecPrepend(player->getPeerId());
}

void Server::setIpBanned(const std::string &ip, const std::string &name)
{
	m_banmanager->add(ip, name);
}

void Server::unsetIpBanned(const std::string &ip_or_name)
{
	m_banmanager->remove(ip_or_name);
}

std::string Server::getBanDescription(const std::string &ip_or_name)
{
	return m_banmanager->getBanDescription(ip_or_name);
}

void Server::notifyPlayer(const char *name, const std::wstring &msg)
{
	if (!m_env)
		return;
	if (m_admin_nick == name && !m_admin_nick.empty()) {
		m_admin_chat->outgoing_queue.push_back(new ChatEventChat("", msg));
	}
	RemotePlayer *player = m_env->getPlayer(name);
	if (!player) {
		return;
	}
	if (player->getPeerId() == PEER_ID_INEXISTENT)
		return;
	SendChatMessage(player->getPeerId(), ChatMessage(msg));
}

bool Server::showFormspec(const char *playername, const std::string &formspec,
	const std::string &formname)
{
	if (!m_env)
		return false;
	RemotePlayer *player = m_env->getPlayer(playername);
	if (!player)
		return false;
	SendShowFormspecMessage(player->getPeerId(), formspec, formname);
	return true;
}

u32 Server::hudAdd(RemotePlayer *player, HudElement *form)
{
	if (!player)
		return -1;
	u32 id = player->addHud(form);
	SendHUDAdd(player->getPeerId(), id, form);
	return id;
}

bool Server::hudRemove(RemotePlayer *player, u32 id) {
	if (!player)
		return false;
	HudElement* todel = player->removeHud(id);
	if (!todel)
		return false;
	delete todel;
	SendHUDRemove(player->getPeerId(), id);
	return true;
}

bool Server::hudChange(RemotePlayer *player, u32 id, HudElementStat stat, void *data)
{
	if (!player)
		return false;
	SendHUDChange(player->getPeerId(), id, stat, data);
	return true;
}

bool Server::hudSetFlags(RemotePlayer *player, u32 flags, u32 mask)
{
	if (!player)
		return false;
	SendHUDSetFlags(player->getPeerId(), flags, mask);
	player->hud_flags &= ~mask;
	player->hud_flags |= flags;
	PlayerSAO* playersao = player->getPlayerSAO();
	if (!playersao)
		return false;
	m_script->player_event(playersao, "hud_changed");
	return true;
}

bool Server::hudSetHotbarItemcount(RemotePlayer *player, s32 hotbar_itemcount)
{
	if (!player)
		return false;
	if (hotbar_itemcount <= 0 || hotbar_itemcount > HUD_HOTBAR_ITEMCOUNT_MAX)
		return false;
	player->setHotbarItemcount(hotbar_itemcount);
	std::ostringstream os(std::ios::binary);
	writeS32(os, hotbar_itemcount);
	SendHUDSetParam(player->getPeerId(), HUD_PARAM_HOTBAR_ITEMCOUNT, os.str());
	return true;
}

void Server::hudSetHotbarImage(RemotePlayer *player, const std::string &name)
{
	if (!player)
		return;
	player->setHotbarImage(name);
	SendHUDSetParam(player->getPeerId(), HUD_PARAM_HOTBAR_IMAGE, name);
}

void Server::hudSetHotbarSelectedImage(RemotePlayer *player, const std::string &name)
{
	if (!player)
		return;
	player->setHotbarSelectedImage(name);
	SendHUDSetParam(player->getPeerId(), HUD_PARAM_HOTBAR_SELECTED_IMAGE, name);
}

Address Server::getPeerAddress(session_t peer_id)
{
	return m_con->GetPeerAddress(peer_id);
}

void Server::setLocalPlayerAnimations(RemotePlayer *player,
		v2s32 animation_frames[4], f32 frame_speed)
{
	sanity_check(player);
	player->setLocalAnimations(animation_frames, frame_speed);
	SendLocalPlayerAnimations(player->getPeerId(), animation_frames, frame_speed);
}

void Server::setPlayerEyeOffset(RemotePlayer *player, const v3f &first, const v3f &third)
{
	sanity_check(player);
	player->eye_offset_first = first;
	player->eye_offset_third = third;
	SendEyeOffset(player->getPeerId(), first, third);
}

void Server::setSky(RemotePlayer *player, const SkyboxParams &params)
{
	sanity_check(player);
	player->setSky(params);
	SendSetSky(player->getPeerId(), params);
}

void Server::setSun(RemotePlayer *player, const SunParams &params)
{
	sanity_check(player);
	player->setSun(params);
	SendSetSun(player->getPeerId(), params);
}

void Server::setMoon(RemotePlayer *player, const MoonParams &params)
{
	sanity_check(player);
	player->setMoon(params);
	SendSetMoon(player->getPeerId(), params);
}

void Server::setStars(RemotePlayer *player, const StarParams &params)
{
	sanity_check(player);
	player->setStars(params);
	SendSetStars(player->getPeerId(), params);
}

void Server::setClouds(RemotePlayer *player, const CloudParams &params)
{
	sanity_check(player);
	player->setCloudParams(params);
	SendCloudParams(player->getPeerId(), params);
}

bool Server::overrideDayNightRatio(RemotePlayer *player, bool do_override,
	float ratio)
{
	if (!player)
		return false;
	player->overrideDayNightRatio(do_override, ratio);
	SendOverrideDayNightRatio(player->getPeerId(), do_override, ratio);
	return true;
}

void Server::notifyPlayers(const std::wstring &msg)
{
	SendChatMessage(PEER_ID_INEXISTENT, ChatMessage(msg));
}

void Server::spawnParticle(const std::string &playername, v3f pos,
	v3f velocity, v3f acceleration,
	float expirationtime, float size, bool
	collisiondetection, bool collision_removal, bool object_collision,
	bool vertical, const std::string &texture,
	const struct TileAnimationParams &animation, u8 glow)
{
	if (!m_env)
		return;
	session_t peer_id = PEER_ID_INEXISTENT;
	u16 proto_ver = 0;
	if (!playername.empty()) {
		RemotePlayer *player = m_env->getPlayer(playername.c_str());
		if (!player)
			return;
		peer_id = player->getPeerId();
		proto_ver = player->protocol_version;
	}
	SendSpawnParticle(peer_id, proto_ver, pos, velocity, acceleration,
			expirationtime, size, collisiondetection, collision_removal,
			object_collision, vertical, texture, animation, glow);
}

u32 Server::addParticleSpawner(u16 amount, float spawntime,
	v3f minpos, v3f maxpos, v3f minvel, v3f maxvel, v3f minacc, v3f maxacc,
	float minexptime, float maxexptime, float minsize, float maxsize,
	bool collisiondetection, bool collision_removal, bool object_collision,
	ServerActiveObject *attached, bool vertical, const std::string &texture,
	const std::string &playername, const struct TileAnimationParams &animation,
	u8 glow)
{
	if (!m_env)
		return -1;
	session_t peer_id = PEER_ID_INEXISTENT;
	u16 proto_ver = 0;
	if (!playername.empty()) {
		RemotePlayer *player = m_env->getPlayer(playername.c_str());
		if (!player)
			return -1;
		peer_id = player->getPeerId();
		proto_ver = player->protocol_version;
	}
	u16 attached_id = attached ? attached->getId() : 0;
	u32 id;
	if (attached_id == 0)
		id = m_env->addParticleSpawner(spawntime);
	else
		id = m_env->addParticleSpawner(spawntime, attached_id);
	SendAddParticleSpawner(peer_id, proto_ver, amount, spawntime,
		minpos, maxpos, minvel, maxvel, minacc, maxacc,
		minexptime, maxexptime, minsize, maxsize, collisiondetection,
		collision_removal, object_collision, attached_id, vertical,
		texture, id, animation, glow);
	return id;
}

void Server::deleteParticleSpawner(const std::string &playername, u32 id)
{
	if (!m_env)
		throw ServerError("Can't delete particle spawners during initialisation!");
	session_t peer_id = PEER_ID_INEXISTENT;
	if (!playername.empty()) {
		RemotePlayer *player = m_env->getPlayer(playername.c_str());
		if (!player)
			return;
		peer_id = player->getPeerId();
	}
	m_env->deleteParticleSpawner(id);
	SendDeleteParticleSpawner(peer_id, id);
}

Inventory* Server::createDetachedInventory(const std::string &name, const std::string &player)
{
	if(m_detached_inventories.count(name) > 0){
		infostream<<"Server clearing detached inventory \""<<name<<"\""<<std::endl;
		delete m_detached_inventories[name];
	} else {
		infostream<<"Server creating detached inventory \""<<name<<"\""<<std::endl;
	}
	Inventory *inv = new Inventory(m_itemdef);
	sanity_check(inv);
	m_detached_inventories[name] = inv;
	if (!player.empty())
		m_detached_inventories_player[name] = player;
	sendDetachedInventory(name,PEER_ID_INEXISTENT);
	return inv;
}

bool Server::removeDetachedInventory(const std::string &name)
{
	const auto &inv_it = m_detached_inventories.find(name);
	if (inv_it == m_detached_inventories.end())
		return false;
	delete inv_it->second;
	m_detached_inventories.erase(inv_it);
	if (!m_env)
		return true;
	const auto &player_it = m_detached_inventories_player.find(name);
	if (player_it != m_detached_inventories_player.end()) {
		RemotePlayer *player = m_env->getPlayer(player_it->second.c_str());
		if (player && player->getPeerId() != PEER_ID_INEXISTENT)
			sendDetachedInventory(name, player->getPeerId());
		m_detached_inventories_player.erase(player_it);
	} else {
		sendDetachedInventory(name, PEER_ID_INEXISTENT);
	}
	return true;
}

bool Server::rollbackRevertActions(const std::list<RollbackAction> &actions,
		std::list<std::string> *log)
{
	infostream<<"Server::rollbackRevertActions(len="<<actions.size()<<")"<<std::endl;
	ServerMap *map = (ServerMap*)(&m_env->getMap());
	if (actions.empty()) {
		assert(log);
		log->push_back("Nothing to do.");
		return false;
	}
	int num_tried = 0;
	int num_failed = 0;
	for (const RollbackAction &action : actions) {
		num_tried++;
		bool success = action.applyRevert(map, this, this);
		if(!success){
			num_failed++;
			std::ostringstream os;
			os<<"Revert of step ("<<num_tried<<") "<<action.toString()<<" failed";
			infostream<<"Map::rollbackRevertActions(): "<<os.str()<<std::endl;
			if (log)
				log->push_back(os.str());
		}else{
			std::ostringstream os;
			os<<"Successfully reverted step ("<<num_tried<<") "<<action.toString();
			infostream<<"Map::rollbackRevertActions(): "<<os.str()<<std::endl;
			if (log)
				log->push_back(os.str());
		}
	}
	infostream<<"Map::rollbackRevertActions(): "<<num_failed<<"/"<<num_tried
			<<" failed"<<std::endl;
	return num_failed <= num_tried/2;
}

IItemDefManager *Server::getItemDefManager()
{
	return m_itemdef;
}

const NodeDefManager *Server::getNodeDefManager()
{
	return m_nodedef;
}

ICraftDefManager *Server::getCraftDefManager()
{
	return m_craftdef;
}

u16 Server::allocateUnknownNodeId(const std::string &name)
{
	return m_nodedef->allocateDummy(name);
}

IWritableItemDefManager *Server::getWritableItemDefManager()
{
	return m_itemdef;
}

NodeDefManager *Server::getWritableNodeDefManager()
{
	return m_nodedef;
}

IWritableCraftDefManager *Server::getWritableCraftDefManager()
{
	return m_craftdef;
}

const std::vector<ModSpec> & Server::getMods() const
{
	return m_modmgr->getMods();
}

const ModSpec *Server::getModSpec(const std::string &modname) const
{
	return m_modmgr->getModSpec(modname);
}

void Server::getModNames(std::vector<std::string> &modlist)
{
	m_modmgr->getModNames(modlist);
}

std::string Server::getBuiltinLuaPath()
{
	return porting::path_share + DIR_DELIM + "builtin";
}

std::string Server::getModStoragePath() const
{
	return m_path_world + DIR_DELIM + "mod_storage";
}

v3f Server::findSpawnPos()
{
	ServerMap &map = m_env->getServerMap();
	v3f nodeposf;
	if (g_settings->getV3FNoEx("static_spawnpoint", nodeposf))
		return nodeposf * BS;
	bool is_good = false;
	s32 range_max = map.getMapgenParams()->getSpawnRangeMax();
	for (s32 i = 0; i < 4000 && !is_good; i++) {
		s32 range = MYMIN(1 + i, range_max);
		v2s16 nodepos2d = v2s16(
			-range + (myrand() % (range * 2)),
			-range + (myrand() % (range * 2)));
		s16 spawn_level = m_emerge->getSpawnLevelAtPoint(nodepos2d);
		if (spawn_level >= MAX_MAP_GENERATION_LIMIT ||
				spawn_level <= -MAX_MAP_GENERATION_LIMIT)
			continue;
		v3s16 nodepos(nodepos2d.X, spawn_level, nodepos2d.Y);
		s32 air_count = 0;
		for (s32 i = 0; i < 8; i++) {
			v3s16 blockpos = getNodeBlockPos(nodepos);
			map.emergeBlock(blockpos, true);
			content_t c = map.getNode(nodepos).getContent();
			if (m_nodedef->get(c).drawtype == NDT_AIRLIKE || c == CONTENT_IGNORE) {
				air_count++;
				if (air_count >= 2) {
					nodepos.Y--;
					nodeposf = intToFloat(nodepos, BS);
					if (objectpos_over_limit(nodeposf))
						break;
					is_good = true;
					break;
				}
			} else {
				air_count = 0;
			}
			nodepos.Y++;
		}
	}
	if (is_good)
		return nodeposf;
	return v3f(0.0f, 0.0f, 0.0f);
}

void Server::requestShutdown(const std::string &msg, bool reconnect, float delay)
{
	if (delay == 0.0f) {
		m_shutdown_state.is_requested = true;
		infostream << "*** Immediate Server shutdown requested." << std::endl;
	} else if (delay < 0.0f && m_shutdown_state.isTimerRunning()) {
		m_shutdown_state.reset();
		std::wstringstream ws;
		ws << L"*** Server shutdown canceled.";
		infostream << wide_to_utf8(ws.str()).c_str() << std::endl;
		SendChatMessage(PEER_ID_INEXISTENT, ws.str());
		return;
	} else if (delay > 0.0f) {
		std::wstringstream ws;
		ws << L"*** Server shutting down in "
				<< duration_to_string(myround(delay)).c_str()
				<< ".";
		infostream << wide_to_utf8(ws.str()).c_str() << std::endl;
		SendChatMessage(PEER_ID_INEXISTENT, ws.str());
	}
	m_shutdown_state.trigger(delay, msg, reconnect);
}

PlayerSAO* Server::emergePlayer(const char *name, session_t peer_id, u16 proto_version)
{
	RemotePlayer *player = m_env->getPlayer(name);
	if (player && player->getPeerId() != PEER_ID_INEXISTENT) {
		infostream<<"emergePlayer(): Player already connected"<<std::endl;
		return NULL;
	}
	if (m_env->getPlayer(peer_id)) {
		infostream<<"emergePlayer(): Player with wrong name but same"
				" peer_id already exists"<<std::endl;
		return NULL;
	}
	if (!player) {
		player = new RemotePlayer(name, idef());
	}
	bool newplayer = false;
	PlayerSAO *playersao = m_env->loadPlayer(player, &newplayer, peer_id, isSingleplayer());
	playersao->finalize(player, getPlayerEffectivePrivs(player->getName()));
	player->protocol_version = proto_version;
	if (newplayer) {
		m_script->on_newplayer(playersao);
	}
	return playersao;
}

bool Server::registerModStorage(ModMetadata *storage)
{
	if (m_mod_storages.find(storage->getModName()) != m_mod_storages.end()) {
		errorstream << "Unable to register same mod storage twice. Storage name: "
				<< storage->getModName() << std::endl;
		return false;
	}
	m_mod_storages[storage->getModName()] = storage;
	return true;
}

void Server::unregisterModStorage(const std::string &name)
{
	std::unordered_map<std::string, ModMetadata *>::const_iterator it = m_mod_storages.find(name);
	if (it != m_mod_storages.end()) {
		it->second->save(getModStoragePath());
		m_mod_storages.erase(name);
	}
}

void dedicated_server_loop(Server &server, bool &kill)
{
	verbosestream<<"dedicated_server_loop()"<<std::endl;
	IntervalLimiter m_profiler_interval;
	static thread_local const float steplen =
			g_settings->getFloat("dedicated_server_step");
	static thread_local const float profiler_print_interval =
			g_settings->getFloat("profiler_print_interval");
	for(;;) {
		sleep_ms((int)(steplen*1000.0));
		server.step(steplen);
		if (server.isShutdownRequested() || kill)
			break;
		if (profiler_print_interval != 0) {
			if(m_profiler_interval.step(steplen, profiler_print_interval))
			{
				infostream<<"Profiler:"<<std::endl;
				g_profiler->print(infostream);
				g_profiler->clear();
			}
		}
	}
	infostream << "Dedicated server quitting" << std::endl;
#if USE_CURL
	if (g_settings->getBool("server_announce"))
		ServerList::sendAnnounce(ServerList::AA_DELETE,
			server.m_bind_addr.getPort());
#endif
}

bool Server::joinModChannel(const std::string &channel)
{
	return m_modchannel_mgr->joinChannel(channel, PEER_ID_SERVER) &&
			m_modchannel_mgr->setChannelState(channel, MODCHANNEL_STATE_READ_WRITE);
}

bool Server::leaveModChannel(const std::string &channel)
{
	return m_modchannel_mgr->leaveChannel(channel, PEER_ID_SERVER);
}

bool Server::sendModChannelMessage(const std::string &channel, const std::string &message)
{
	if (!m_modchannel_mgr->canWriteOnChannel(channel))
		return false;
	broadcastModChannelMessage(channel, message, PEER_ID_SERVER);
	return true;
}

ModChannel* Server::getModChannel(const std::string &channel)
{
	return m_modchannel_mgr->getModChannel(channel);
}

void Server::broadcastModChannelMessage(const std::string &channel,
		const std::string &message, session_t from_peer)
{
	const std::vector<u16> &peers = m_modchannel_mgr->getChannelPeers(channel);
	if (peers.empty())
		return;
	if (message.size() > STRING_MAX_LEN) {
		warningstream << "ModChannel message too long, dropping before sending "
				<< " (" << message.size() << " > " << STRING_MAX_LEN << ", channel: "
				<< channel << ")" << std::endl;
		return;
	}
	std::string sender;
	if (from_peer != PEER_ID_SERVER) {
		sender = getPlayerName(from_peer);
	}
	NetworkPacket resp_pkt(TOCLIENT_MODCHANNEL_MSG,
			2 + channel.size() + 2 + sender.size() + 2 + message.size());
	resp_pkt << channel << sender << message;
	for (session_t peer_id : peers) {
		if (peer_id == from_peer)
			continue;
		Send(peer_id, &resp_pkt);
	}
	if (from_peer != PEER_ID_SERVER) {
		m_script->on_modchannel_message(channel, sender, message);
	}
}