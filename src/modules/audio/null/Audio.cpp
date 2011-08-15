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

#include "Audio.h"

namespace love
{
namespace audio
{
namespace null
{
	Audio::Audio()
	{
	}

	Audio::~Audio()
	{
	}

	const char * Audio::getName() const
	{
		return "love.audio.null";
	}

	love::audio::Source * Audio::newSource(love::sound::Decoder *)
	{
		return new Source();
	}

	love::audio::Source * Audio::newSource(love::sound::SoundData *)
	{
		return new Source();
	}

	int Audio::getNumSources() const
	{
		return 0;
	}

	int Audio::getMaxSources() const
	{
		return 0;
	}

	void Audio::play(love::audio::Source *)
	{
	}

	void Audio::play()
	{
	}

	void Audio::stop(love::audio::Source *)
	{
	}

	void Audio::stop()
	{
	}

	void Audio::pause(love::audio::Source *)
	{
	}

	void Audio::pause()
	{
	}

	void Audio::resume(love::audio::Source *)
	{
	}

	void Audio::resume()
	{
	}

	void Audio::rewind(love::audio::Source *)
	{
	}

	void Audio::rewind()
	{
	}

	void Audio::setVolume(float volume)
	{
		this->volume = volume;
	}

	float Audio::getVolume() const
	{
		return volume;
	}

	void Audio::getPosition(float *) const
	{
	}

	void Audio::setPosition(float *)
	{
	}

	void Audio::getOrientation(float *) const
	{
	}

	void Audio::setOrientation(float *)
	{
	}

	void Audio::getVelocity(float *) const
	{
	}

	void Audio::setVelocity(float *)
	{
	}
	
	void Audio::record()
	{
	}
	
	love::sound::SoundData * Audio::getRecordedData()
	{
		return NULL;
	}
	
	love::sound::SoundData * Audio::stopRecording(bool)
	{
		return NULL;
	}
	
	bool Audio::canRecord()
	{
		return false;
	}

} // null
} // audio
} // love
