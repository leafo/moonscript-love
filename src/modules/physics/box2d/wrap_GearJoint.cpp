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

#include "wrap_GearJoint.h"

namespace love
{
namespace physics
{
namespace box2d
{
	GearJoint * luax_checkgearjoint(lua_State * L, int idx)
	{
		return luax_checktype<GearJoint>(L, idx, "GearJoint", PHYSICS_GEAR_JOINT_T);
	}

	int w_GearJoint_setRatio(lua_State * L)
	{
		GearJoint * t = luax_checkgearjoint(L, 1);
		float arg1 = (float)luaL_checknumber(L, 2);
		t->setRatio(arg1);
		return 0;
	}
	
	int w_GearJoint_getRatio(lua_State * L)
	{
		GearJoint * t = luax_checkgearjoint(L, 1);
		lua_pushnumber(L, t->getRatio());
		return 1;
	}

	static const luaL_Reg functions[] = {
		{ "setRatio", w_GearJoint_setRatio },
		{ "getRatio", w_GearJoint_getRatio },
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

	int luaopen_gearjoint(lua_State * L)
	{
		return luax_register_type(L, "GearJoint", functions);
	}

} // box2d
} // physics
} // love
