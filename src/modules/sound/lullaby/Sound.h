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



#ifndef LOVE_SOUND_LULLABY_SOUND_H
#define LOVE_SOUND_LULLABY_SOUND_H

// LOVE
#include <sound/Sound.h>
#include <sound/Decoder.h>

namespace love
{
namespace sound
{
namespace lullaby
{
	/**
	* The love.sound.lullaby module is the custom sound decoder module for LOVE. Instead
	* of using an intermediate library like SDL_sound, it interfaces with relevant libraries
	* directly (libmpg123, libmodplug, libFLAC, etc). 
	* 
	* It was Mike that came up with the name Lullaby, which we both instantly recognized as awesome. 
	**/
	class Sound : public love::sound::Sound
	{
	public:

		/**
		* Constructor. Initializes relevant libraries.
		**/
		Sound();

		/**
		* Destructor. Deinitializes relevant libraries.
		**/
		virtual ~Sound();

		/// @copydoc love::Module::getName
		const char * getName() const;
		
		/// @copydoc love::sound::Sound::newDecoder
		sound::Decoder * newDecoder(love::filesystem::File * file, int bufferSize);

	}; // Sound

} // lullaby
} // sound
} // love

#endif // LOVE_SOUND_LULLABY_SOUND_H