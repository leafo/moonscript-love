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

#include "wrap_MouseJoint.h"

namespace love
{
namespace physics
{
namespace box2d
{
	MouseJoint * luax_checkmousejoint(lua_State * L, int idx)
	{
		return luax_checktype<MouseJoint>(L, idx, "MouseJoint", PHYSICS_MOUSE_JOINT_T);
	}

	int w_MouseJoint_setTarget(lua_State * L)
	{
		MouseJoint * t = luax_checkmousejoint(L, 1);
		float x = (float)luaL_checknumber(L, 2);
		float y = (float)luaL_checknumber(L, 3);
		t->setTarget(x, y);
		return 0;
	}

	int w_MouseJoint_getTarget(lua_State * L)
	{
		MouseJoint * t = luax_checkmousejoint(L, 1);
		lua_remove(L, 1);
		return t->getTarget(L);
	}

	int w_MouseJoint_setMaxForce(lua_State * L)
	{
		MouseJoint * t = luax_checkmousejoint(L, 1);
		float f = (float)luaL_checknumber(L, 2);
		t->setMaxForce(f);
		return 0;
	}

	int w_MouseJoint_getMaxForce(lua_State * L)
	{
		MouseJoint * t = luax_checkmousejoint(L, 1);
		lua_pushnumber(L, t->getMaxForce());
		return 1;
	}

	static const luaL_Reg functions[] = {
		{ "setTarget", w_MouseJoint_setTarget },
		{ "getTarget", w_MouseJoint_getTarget },
		{ "setMaxForce", w_MouseJoint_setMaxForce },
		{ "getMaxForce", w_MouseJoint_getMaxForce },
		// From Joint.
		{ "getType", w_Joint_getType },
		{ "getAnchors", w_Joint_getAnchors },
		{ "getReactionForce", w_Joint_getReactionForce },
		{ "getReactionTorque", w_Joint_getReactionTorque },
		{ "setCollideConnected", w_Joint_setCollideConnected },
		{ "getCollideConnected", w_Joint_getCollideConnected },
		{ "destroy", w_Joint_destroy },
		{ 0, 0 }
	};

	int luaopen_mousejoint(lua_State * L)
	{
		return luax_register_type(L, "MouseJoint", functions);
	}

} // box2d
} // physics
} // love
