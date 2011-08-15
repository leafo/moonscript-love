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

#ifndef LOVE_VERSION_H
#define LOVE_VERSION_H

namespace love
{
	// Version stuff.
	const int VERSION_MAJOR = 0;
	const int VERSION_MINOR = 8;
	const int VERSION_REV = 0;
	const int VERSION = VERSION_MAJOR*100 + VERSION_MINOR*10 + VERSION_REV;
	const int VERSION_COMPATIBILITY[] =  { VERSION, 072, 071, 070, 0 };
	const char * VERSION_STR = "0.8.0";
	const char * VERSION_CODENAME = "Rubber Piggy";

} // love

#endif // LOVE_VERSION_H
