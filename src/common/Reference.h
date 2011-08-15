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

#ifndef LOVE_REFERENCE_H
#define LOVE_REFERENCE_H

// LOVE
#include "runtime.h"

namespace love
{
	/**
	* This class wraps the reference functionality built into
	* Lua, which allows C++ code to refer to Lua variables.
	**/
	class Reference
	{
	private:

		// The Lua state in which the reference resides.
		lua_State * L;

		// Index to the Lua reference.
		int idx;

	public:

		/**
		* Creates the reference object, but does not create
		* the actual reference.
		**/
		Reference();

		/**
		* Creates the object and a reference to the value 
		* on the top of the stack.
		**/
		Reference(lua_State * L);

		/**
		* Deletes the reference, if any.
		**/
		virtual ~Reference();
		
		/**
		* Creates a reference to the value on the
		* top of the stack.
		**/ 
		void ref(lua_State * L);

		/**
		* Unrefs the reference, if any.
		**/
		void unref();

		/**
		* Pushes the referred value onto the stack.
		**/
		void push();

		/**
		* Gets the Lua state associated with this
		* reference.
		**/
		lua_State * getL();
	};

} // love

#endif // LOVE_REFERENCE_H
