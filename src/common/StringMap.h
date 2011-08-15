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

#ifndef LOVE_STRING_MAP_H
#define LOVE_STRING_MAP_H

#include "Exception.h"

namespace love
{
	template<typename T, unsigned SIZE>
	class StringMap
	{
	private:

		struct Record
		{
			const char * key;
			T value;
			bool set;
			Record() : set(false) {}
		};

		const static unsigned MAX = SIZE*2;

		Record records[MAX];
		const char * reverse[SIZE];

	public:

		struct Entry
		{
			const char * key;
			T value;
		};

		StringMap(Entry * entries, unsigned num)
		{

			for(unsigned i = 0; i < SIZE; ++i)
				reverse[i] = 0;

			unsigned n = num/sizeof(Entry);

			for(unsigned i = 0; i < n; ++i)
			{
				add(entries[i].key, entries[i].value);
			}
		}

		bool streq(const char * a, const char * b)
		{
			while(*a != 0 && *b != 0)
			{
				if(*a != *b)
					return false;
				++a;
				++b;
			}

			return (*a == 0 && *b == 0);
		}

		bool find(const char * key, T & t)
		{
			//unsigned str_hash = djb2(key);

			for(unsigned i = 0; i < MAX; ++i)
			{
				//unsigned str_i = (str_hash + i) % MAX; //this isn't used, is this intentional?

				if(records[i].set && streq(records[i].key, key))
				{
					t = records[i].value;
					return true;
				}
			}

			return false;
		}

		bool find(T key, const char *& str)
		{
			unsigned index = (unsigned)key;

			if(index >= SIZE)
				return false;
			
			if(reverse[index] != 0)
			{
				str = reverse[index];
				return true;
			}
			else
			{
				return false;
			}
		}

		bool add(const char * key, T value)
		{
			unsigned str_hash = djb2(key);
			bool inserted = false;
			
			for(unsigned i = 0; i < MAX; ++i)
			{
				unsigned str_i = (str_hash + i) % MAX;

				if(!records[str_i].set)
				{
					inserted = true;
					records[str_i].set = true;
					records[str_i].key = key;
					records[str_i].value = value;
					break;
				}
			}

			unsigned index = (unsigned)value;

			if(index >= SIZE)
			{
				printf("\nConstant %s out of bounds with %i!\n", key, index);
				return false;
			}

			reverse[index] = key;

			return inserted;
		}

		unsigned djb2(const char * key)
		{
			unsigned hash = 5381;
			int c;

			while ((c = *key++))
				hash = ((hash << 5) + hash) + c;

			return hash;
		}

	}; // StringMap

} // love

#endif // LOVE_STRING_MAP_H
