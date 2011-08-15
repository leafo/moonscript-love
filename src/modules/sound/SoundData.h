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

#ifndef LOVE_SOUND_SOUND_DATA_H
#define LOVE_SOUND_SOUND_DATA_H

// LOVE
#include <filesystem/File.h>

#include "Decoder.h"

namespace love
{	
namespace sound
{
	class SoundData : public love::Data
	{
	private:

		char * data;
		int size;

		int sampleRate;
		int bits;
		int channels;

	public:

		SoundData(Decoder * decoder);
		SoundData(int samples, int sampleRate, int bits, int channels);
		SoundData(void * d, int samples, int sampleRate, int bits, int channels);

		virtual ~SoundData();

		// Implements Data.
		void * getData() const;
		int getSize() const;
	
		virtual int getChannels() const;
		virtual int getBits() const;
		virtual int getSampleRate() const;

		void setSample(int i, float sample);
		float getSample(int i) const;

	}; // SoundData

} // sound
} // love

#endif // LOVE_SOUND_SOUND_DATA_H
