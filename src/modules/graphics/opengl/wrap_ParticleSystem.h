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

#ifndef LOVE_GRAPHICS_OPENGL_WRAP_PARTICLE_SYSTEM_H
#define LOVE_GRAPHICS_OPENGL_WRAP_PARTICLE_SYSTEM_H

// LOVE
#include <common/runtime.h>
#include "wrap_Image.h"
#include "ParticleSystem.h"

namespace love
{
namespace graphics
{
namespace opengl
{
	ParticleSystem * luax_checkparticlesystem(lua_State * L, int idx);
	int w_ParticleSystem_setSprite(lua_State * L);
	int w_ParticleSystem_setBufferSize(lua_State * L);
	int w_ParticleSystem_setEmissionRate(lua_State * L);
	int w_ParticleSystem_setLifetime(lua_State * L);
	int w_ParticleSystem_setParticleLife(lua_State * L);
	int w_ParticleSystem_setPosition(lua_State * L);
	int w_ParticleSystem_setDirection(lua_State * L);
	int w_ParticleSystem_setSpread(lua_State * L);
	int w_ParticleSystem_setRelativeDirection(lua_State * L);
	int w_ParticleSystem_setSpeed(lua_State * L);
	int w_ParticleSystem_setGravity(lua_State * L);
	int w_ParticleSystem_setRadialAcceleration(lua_State * L);
	int w_ParticleSystem_setTangentialAcceleration(lua_State * L);
	int w_ParticleSystem_setSizes(lua_State * L);
	int w_ParticleSystem_setSizeVariation(lua_State * L);
	int w_ParticleSystem_setRotation(lua_State * L);
	int w_ParticleSystem_setSpin(lua_State * L);
	int w_ParticleSystem_setSpinVariation(lua_State * L);
	int w_ParticleSystem_setColors(lua_State * L);
	int w_ParticleSystem_setOffset(lua_State * L);
	int w_ParticleSystem_getX(lua_State * L);
	int w_ParticleSystem_getY(lua_State * L);
	int w_ParticleSystem_getDirection(lua_State * L);
	int w_ParticleSystem_getSpread(lua_State * L);
	int w_ParticleSystem_getOffsetX(lua_State * L);
	int w_ParticleSystem_getOffsetY(lua_State * L);
	int w_ParticleSystem_count(lua_State * L);
	int w_ParticleSystem_start(lua_State * L);
	int w_ParticleSystem_stop(lua_State * L);
	int w_ParticleSystem_pause(lua_State * L);
	int w_ParticleSystem_reset(lua_State * L);
	int w_ParticleSystem_isActive(lua_State * L);
	int w_ParticleSystem_isEmpty(lua_State * L);
	int w_ParticleSystem_isFull(lua_State * L);
	int w_ParticleSystem_update(lua_State * L);
	int luaopen_particlesystem(lua_State * L);

} // opengl
} // graphics
} // love

#endif // LOVE_GRAPHICS_OPENGL_WRAP_PARTICLE_SYSTEM_H
