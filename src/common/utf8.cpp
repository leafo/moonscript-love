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

#include "utf8.h"

#ifdef LOVE_WINDOWS

namespace love
{
	std::string to_utf8(LPCWSTR wstr)
	{
		size_t wide_len = wcslen(wstr)+1;

		// Get size in UTF-8.
		int utf8_size = WideCharToMultiByte(CP_UTF8, 0, wstr, wide_len, 0, 0, 0, 0);

		char * utf8_str = new char[utf8_size];

		// Convert to UTF-8.
		int ok = WideCharToMultiByte(CP_UTF8, 0, wstr, wide_len, utf8_str, utf8_size, 0, 0);

		if(!ok)
		{
			delete [] utf8_str;
		}

		return ok ? std::string(utf8_str) : std::string();
	}

	void replace_char(std::string & str, char find, char replace)
	{
		int length = str.length();

		for(int i = 0; i<length; i++)
		{
			if(str[i] == find)
				str[i] = replace;
		}
	}

} // love

#endif // LOVE_WINDOWS