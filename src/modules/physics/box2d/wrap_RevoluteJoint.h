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

#ifndef LOVE_PHYSICS_BOX2D_WRAP_REVOLUTE_JOINT_H
#define LOVE_PHYSICS_BOX2D_WRAP_REVOLUTE_JOINT_H

// LOVE
#include <common/runtime.h>
#include "wrap_Joint.h"
#include "RevoluteJoint.h"

namespace love
{
namespace physics
{
namespace box2d
{
	RevoluteJoint * luax_checkrevolutejoint(lua_State * L, int idx);
	int w_RevoluteJoint_getJointAngle(lua_State * L);
	int w_RevoluteJoint_getJointSpeed(lua_State * L);
	int w_RevoluteJoint_setMotorEnabled(lua_State * L);
	int w_RevoluteJoint_isMotorEnabled(lua_State * L);
	int w_RevoluteJoint_setMaxMotorTorque(lua_State * L);
	int w_RevoluteJoint_getMaxMotorTorque(lua_State * L);
	int w_RevoluteJoint_setMotorSpeed(lua_State * L);
	int w_RevoluteJoint_getMotorSpeed(lua_State * L);
	int w_RevoluteJoint_getMotorTorque(lua_State * L);
	int w_RevoluteJoint_setLimitsEnabled(lua_State * L);
	int w_RevoluteJoint_isLimitsEnabled(lua_State * L);
	int w_RevoluteJoint_setUpperLimit(lua_State * L);
	int w_RevoluteJoint_setLowerLimit(lua_State * L);
	int w_RevoluteJoint_setLimits(lua_State * L);
	int w_RevoluteJoint_getLowerLimit(lua_State * L);
	int w_RevoluteJoint_getUpperLimit(lua_State * L);
	int w_RevoluteJoint_getLimits(lua_State * L);
	int luaopen_revolutejoint(lua_State * L);

} // box2d
} // physics
} // love

#endif // LOVE_PHYSICS_BOX2D_WRAP_REVOLUTE_JOINT_H
