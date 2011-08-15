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

#ifndef LOVE_IMAGE_DEVIL_IMAGE_H
#define LOVE_IMAGE_DEVIL_IMAGE_H

// LOVE
#include <image/Image.h>

namespace love
{
namespace image
{
namespace devil
{
	class Image : public love::image::Image
	{
	public:

		Image();
		 ~Image();

		// Implements Module.
		const char * getName() const;
		
		love::image::ImageData * newImageData(love::filesystem::File * file);
		love::image::ImageData * newImageData(Data * data);
		love::image::ImageData * newImageData(int width, int height);
		love::image::ImageData * newImageData(int width, int height, void *data);

	}; // Image

} // devil
} // image
} // love

#endif // LOVE_IMAGE_DEVIL_IMAGE_H