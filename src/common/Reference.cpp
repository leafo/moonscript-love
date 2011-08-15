/**
* Copyright (c) 2006-2011 LOVE Development Team
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

#include "Reference.h"

namespace love
{
	Reference::Reference()
		: L(0), idx(LUA_REFNIL)
	{
	}

	Reference::Reference(lua_State * L)
		: L(0), idx(LUA_REFNIL)
	{
		ref(L);
	}

	Reference::~Reference()
	{
		unref();
	}

	void Reference::ref(lua_State * L)
	{
		unref(); // Just to be safe.
		this->L = L;
		idx = luaL_ref(L, LUA_GLOBALSINDEX);
	}

	void Reference::unref()
	{
		if(idx != LUA_REFNIL)
		{
			luaL_unref(L, LUA_GLOBALSINDEX, idx);
			idx = LUA_REFNIL;
		}
	}

	void Reference::push()
	{
		if(idx != LUA_REFNIL)
			lua_rawgeti(L, LUA_GLOBALSINDEX, idx);
		else
			lua_pushnil(L);
	}

	lua_State * Reference::getL()
	{
		return L;
	}

} // love
