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

#include "wrap_File.h"

#include <common/Data.h>
#include <common/Exception.h>

namespace love
{
namespace filesystem
{
namespace physfs
{
	File * luax_checkfile(lua_State * L, int idx)
	{
		return luax_checktype<File>(L, idx, "File", FILESYSTEM_FILE_T);
	}

	int w_File_getSize(lua_State * L)
	{
		File * t = luax_checkfile(L, 1);
		try
		{
			lua_pushinteger(L, t->getSize());
		}
		catch (Exception & e)
		{
			return luaL_error(L, e.what());
		}
		return 1;
	}

	int w_File_open(lua_State * L)
	{
		File * file = luax_checkfile(L, 1);
		File::Mode mode;

		if(!File::getConstant(luaL_checkstring(L, 2), mode))
			return luaL_error(L, "Incorrect file open mode: %s", luaL_checkstring(L, 2));

		try
		{
			lua_pushboolean(L, file->open(mode) ? 1 : 0);
		}
		catch(Exception e)
		{
			return luaL_error(L, e.what());
		}

		return 1;
	}

	int w_File_close(lua_State * L)
	{
		File * file = luax_checkfile(L, 1);
		lua_pushboolean(L, file->close() ? 1 : 0);
		return 1;
	}

	int w_File_read(lua_State * L)
	{
		File * file = luax_checkfile(L, 1);
		Data * d = 0;

		try
		{
			d = file->read(luaL_optint(L, 2, file->getSize()));
		}
		catch(Exception e)
		{
			return luaL_error(L, e.what());
		}

		lua_pushlstring(L, (const char*) d->getData(), d->getSize());
		lua_pushnumber(L, d->getSize());
		d->release();
		return 2;
	}

	int w_File_write(lua_State * L)
	{
		File * file = luax_checkfile(L, 1);
		bool result;
		if ( file->getMode() == File::CLOSED )
			return luaL_error(L, "File is not open.");
		if ( lua_isstring(L, 2) )
		{
			try
			{
				result = file->write(lua_tostring(L, 2), luaL_optint(L, 3, lua_objlen(L, 2)));
			}
			catch(Exception e)
			{
				return luaL_error(L, e.what());
			}
			
		}
		else if( luax_istype(L, 2, DATA_T)) {
			try
			{
				love::Data * data = luax_totype<love::Data>(L, 2, "Data", DATA_T);
				result = file->write(data, luaL_optint(L, 3, data->getSize()));
			} catch(Exception e)
			{
				return luaL_error(L, e.what());
			}
		}
		else
		{
			return luaL_error(L, "String or data expected.");
		}
		lua_pushboolean(L, result);
		return 1;
	}

	int w_File_eof(lua_State * L)
	{
		File * file = luax_checkfile(L, 1);
		lua_pushboolean(L, file->eof() ? 1 : 0);
		return 1;
	}

	int w_File_tell(lua_State * L)
	{
		File * file = luax_checkfile(L, 1);
		lua_pushinteger(L, file->tell());
		return 1;
	}

	int w_File_seek(lua_State * L)
	{
		File * file = luax_checkfile(L, 1);
		int pos = luaL_checkinteger(L, 2);
		lua_pushboolean(L, file->seek(pos) ? 1 : 0);
		return 1;
	}

	//yes, the following two are copy-pasted and slightly edited

	int w_File_lines(lua_State * L)
	{
		File * file;

		if(luax_istype(L, 1, FILESYSTEM_FILE_T))
		{
			file = luax_checktype<File>(L, 1, "File", FILESYSTEM_FILE_T);
			lua_pushnumber(L, 0); // 0 = do not close.
		}
		else
			return luaL_error(L, "Expected file handle.");

		// Reset the file position.
		if(!file->seek(0))
		return luaL_error(L, "File does not appear to be open.\n");

		lua_pushcclosure(L, Filesystem::lines_i, 2);
		return 1;
	}

	static const luaL_Reg functions[] = { 
			{ "getSize", w_File_getSize },
			{ "open", w_File_open },
			{ "close", w_File_close },
			{ "read", w_File_read },
			{ "write", w_File_write },
			{ "eof", w_File_eof },
			{ "tell", w_File_tell },
			{ "seek", w_File_seek },
			{ "lines", w_File_lines },
			{ 0, 0 }
	};

	int luaopen_file(lua_State * L)
	{
		return luax_register_type(L, "File", functions);
	}
	
} // physfs
} // filesystem
} // love
