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

#ifndef LOVE_JOYSTICK_SDL_WRAP_JOYSTICK_H
#define LOVE_JOYSTICK_SDL_WRAP_JOYSTICK_H

// LOVE
#include <common/config.h>
#include "Joystick.h"

namespace love
{
namespace joystick
{
namespace sdl
{
	int w_getNumJoysticks(lua_State * L);
	int w_getName(lua_State * L);
	int w_open(lua_State * L);
	int w_isOpen(lua_State * L);
	int w_getNumAxes(lua_State * L);
	int w_getNumBalls(lua_State * L);
	int w_getNumButtons(lua_State * L);
	int w_getNumHats(lua_State * L);
	int w_getAxis(lua_State * L);
	int w_getAxes(lua_State * L);
	int w_getBall(lua_State * L);
	int w_isDown(lua_State * L);
	int w_getHat(lua_State * L);
	int w_close(lua_State * L);
	extern "C" LOVE_EXPORT int luaopen_love_joystick(lua_State * L);

} // sdl
} // joystick
} // love

#endif // LOVE_JOYSTICK_SDL_WRAP_JOYSTICK_H
