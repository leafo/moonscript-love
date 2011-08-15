/**
* Copyright (c) 2006-2010 LOVE Development Team
*
* This software is provided 'as-is', without any express or implied
* warranty.  In no event will the authors be held liable for any damages
* arising from the use of this software.
*
* Permission is granted to anyone to use this software for any purpose,
* including commercial applications, and to alter it and redistribute it
* freely, subject to the following restrictions:
*
* 1. The origin of this software must not be misrepresented; you must not
*    claim that you wrote the original software. If you use this software
*    in a product, an acknowledgment in the product documentation would be
*    appreciated but is not required.
* 2. Altered source versions must be plainly marked as such, and must not be
*    misrepresented as being the original software.
* 3. This notice may not be removed or altered from any source distribution.
**/

#include "wrap_Thread.h"

// anonymous namespace for getting an std::string from the stack
// that may contain embedded NULLs
namespace
{
	std::string luax_checklstring(lua_State *L, int idx)
	{
		size_t len;
		const char* str = luaL_checklstring(L, idx, &len);
		return std::string(str, len);
	}
}

namespace love
{
namespace thread
{
	Thread *luax_checkthread(lua_State *L, int idx)
	{
		return luax_checktype<Thread>(L, idx, "Thread", THREAD_THREAD_T);
	}

	int w_Thread_start(lua_State *L)
	{
		Thread *t = luax_checkthread(L, 1);
		t->start();
		return 0;
	}

	int w_Thread_kill(lua_State *L)
	{
		Thread *t = luax_checkthread(L, 1);
		t->kill();
		return 0;
	}

	int w_Thread_wait(lua_State *L)
	{
		Thread *t = luax_checkthread(L, 1);
		t->wait();
		return 0;
	}

	int w_Thread_getName(lua_State *L)
	{
		Thread *t = luax_checkthread(L, 1);
		// allow names containing \0
		lua_pushlstring(L, t->getName().c_str(), t->getName().length());
		return 1;
	}

	bool __pushThreadVariant(lua_State *L, ThreadVariant *v)
	{
		if (!v)
		{
			lua_pushnil(L);
			return false;
		}
		switch(v->type)
		{
			case BOOLEAN:
				lua_pushboolean(L, v->data.boolean);
				break;
			case NUMBER:
				lua_pushnumber(L, v->data.number);
				break;
			case STRING:
				lua_pushlstring(L, v->data.string.str, v->data.string.len);
				break;
			case LUSERDATA:
				lua_pushlightuserdata(L, v->data.userdata);
				break;
			case FUSERDATA:
				if (v->udatatype != INVALID_ID)
				{
					const char *name = NULL;
					love::types.find(v->udatatype, name);
					((love::Object *) v->data.userdata)->retain();
					luax_newtype(L, name, v->flags, v->data.userdata);
				}
				else
					lua_pushlightuserdata(L, v->data.userdata);
				// I know this is not the same
				// sadly, however, it's the most
				// I can do (at the moment).
				break;
			default:
				lua_pushnil(L);
				break;
		}
		return true;
	}

	int w_Thread_get(lua_State *L)
	{
		Thread *t = luax_checkthread(L, 1);
		std::string name = luax_checklstring(L, 2);
		t->lock();
		ThreadVariant *v = t->get(name);
		t->clear(name);
		t->unlock();
		if (!__pushThreadVariant(L, v))
			return 1;
		t->lock();
		v->release();
		t->unlock();
		return 1;
	}

	int w_Thread_demand(lua_State *L)
	{
		Thread *t = luax_checkthread(L, 1);
		std::string name = luax_checklstring(L, 2);
		t->lock();
		ThreadVariant *v = t->demand(name);
		t->clear(name);
		t->unlock();
		if (!__pushThreadVariant(L, v))
			return 1;
		t->lock();
		v->release();
		t->unlock();
		return 1;
	}

	int w_Thread_peek(lua_State *L)
	{
		Thread *t = luax_checkthread(L, 1);
		std::string name = luax_checklstring(L, 2);
		t->lock();
		ThreadVariant *v = t->get(name);
		t->unlock();
		if (!__pushThreadVariant(L, v))
			return 1;
		t->lock();
		v->release();
		t->unlock();
		return 1;
	}

	Type extractudatatype(lua_State * L, int idx)
        {
                Type t = INVALID_ID;
                if (!lua_isuserdata(L, idx))
                        return t;
                if (luaL_getmetafield (L, idx, "__tostring") == 0)
                        return t;
                lua_pushvalue(L, idx);
                int result = lua_pcall(L, 1, 1, 0);
                if (result == 0)
                        types.find(lua_tostring(L, -1), t);
                if (result == 0 || result == LUA_ERRRUN)
                        lua_pop(L, 1);
                return t;
        }

	int w_Thread_set(lua_State *L)
	{
		Thread *t = luax_checkthread(L, 1);
		std::string name = luax_checklstring(L, 2);
		ThreadVariant *v;
		size_t len;
		const char *str;
		switch(lua_type(L, 3))
		{
			case LUA_TBOOLEAN:
				v = new ThreadVariant(luax_toboolean(L, 3));
				break;
			case LUA_TNUMBER:
				v = new ThreadVariant(lua_tonumber(L, 3));
				break;
			case LUA_TSTRING:
				str = lua_tolstring(L, 3, &len);
				v = new ThreadVariant(str, len);
				break;
			case LUA_TLIGHTUSERDATA:
				v = new ThreadVariant(lua_touserdata(L, 3));
				break;
			case LUA_TUSERDATA:
				v = new ThreadVariant(extractudatatype(L, 3), lua_touserdata(L, 3));
				break;
			default:
				return luaL_error(L, "Expected boolean, number, string or userdata");
		}
		t->set(name, v);
		t->lock();
		v->release();
		t->unlock();
		return 0;
	}

	static const luaL_Reg type_functions[] = {
		{ "start", w_Thread_start },
		{ "kill", w_Thread_kill },
		{ "wait", w_Thread_wait },
		{ "getName", w_Thread_getName },
		{ "get", w_Thread_get },
		{ "demand", w_Thread_demand },
		{ "peek", w_Thread_peek },
		{ "set", w_Thread_set },
		{ 0, 0 }
	};

	int luaopen_thread(lua_State *L)
	{
		return luax_register_type(L, "Thread", type_functions);
	}

	static ThreadModule *instance;

	int w_newThread(lua_State *L)
	{
		std::string name = luax_checklstring(L, 1);
		love::Data *data;
		if (lua_isstring(L, 2))
			luax_convobj(L, 2, "filesystem", "newFile");
		if (luax_istype(L, 2, FILESYSTEM_FILE_T))
		{
			try {
				data = luax_checktype<love::filesystem::File>(L, 2, "File", FILESYSTEM_FILE_T)->read();
			} catch (love::Exception & e) {
				return luaL_error(L, e.what());
			}
		}
		else
			data = luax_checktype<love::Data>(L, 2, "Data", DATA_T);
		Thread *t = instance->newThread(name, data);
		if (!t)
			return luaL_error(L, "A thread with that name already exists.");
		luax_newtype(L, "Thread", THREAD_THREAD_T, (void*)t);
		return 1;
	}

	int w_getThreads(lua_State *L)
	{
		unsigned count = instance->getThreadCount();
		Thread **list = new Thread*[count];
		instance->getThreads(list);
		lua_newtable(L);
		for (unsigned int i = 0; i<count; i++)
		{
			// allow names containing \0
			lua_pushlstring(L, list[i]->getName().c_str(), list[i]->getName().length());
			luax_newtype(L, "Thread", THREAD_THREAD_T, (void*) list[i]);
			list[i]->lock();
			list[i]->retain();
			list[i]->unlock();
			lua_settable(L, -3);
		}
		delete[] list;
		return 1;
	}

	int w_getThread(lua_State *L)
	{
		if (lua_isnoneornil(L, 1))
		{
			lua_getglobal(L, "love");
			lua_getfield(L, -1, "_curthread");
			return 1;
		}
		std::string name = luax_checklstring(L, 1);
		Thread *t = instance->getThread(name);
		if (t)
		{
			luax_newtype(L, "Thread", THREAD_THREAD_T, (void*)t);
			t->lock();
			t->retain();
			t->unlock();
		}
		else
			lua_pushnil(L);
		return 1;
	}


	// List of functions to wrap.
	static const luaL_Reg module_functions[] = {
		{ "newThread", w_newThread },
		{ "getThread", w_getThread },
		{ "getThreads", w_getThreads },
		{ 0, 0 }
	};

	static const lua_CFunction types[] = {
		luaopen_thread,
		0
	};

	int luaopen_love_thread(lua_State *L)
	{
		if(instance == 0)
		{
			try
			{
				instance = new ThreadModule();
				lua_getglobal(L, "love");
				Thread *curthread = instance->getThread("main");
				curthread->lock();
				curthread->retain();
				curthread->unlock();
				luax_newtype(L, "Thread", THREAD_THREAD_T, (void*)curthread);
				lua_setfield(L, -2, "_curthread");
			}
			catch(Exception & e)
			{
				return luaL_error(L, e.what());
			}
		}
		else
			instance->retain();

		WrappedModule w;
		w.module = instance;
		w.name = "thread";
		w.flags = MODULE_T;
		w.functions = module_functions;
		w.types = types;

		return luax_register_module(L, w);
	}
}
}
