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

#ifndef LOVE_SOUND_LULLABY_LIBMPG123_DECODER_H
#define LOVE_SOUND_LULLABY_LIBMPG123_DECODER_H

// LOVE
#include <common/Data.h>
#include "Decoder.h"

// libmpg123
#ifdef LOVE_MACOSX
#include <mpg123/mpg123.h>
#else
#include <mpg123.h>
#endif

namespace love
{
namespace sound
{
namespace lullaby
{
	class Mpg123Decoder : public Decoder
	{
	private:

		mpg123_handle * handle;
		static bool inited;

		int data_offset;
		int data_size;

		int channels;

	public:

		Mpg123Decoder(Data * data, const std::string & ext, int bufferSize);
		virtual ~Mpg123Decoder();

		static bool accepts(const std::string & ext);
		static void quit();

		love::sound::Decoder * clone();
		int decode();
		bool seek(float s);
		bool rewind();
		bool isSeekable();
		int getChannels() const;
		int getBits() const;

	private:

		int feed(int bytes);

	}; // Decoder

} // lullaby
} // sound
} // love

#endif // LOVE_SOUND_LULLABY_LIBMPG123_DECODER_H
