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

#ifndef LOVE_IMAGE_IMAGE_DATA_H
#define LOVE_IMAGE_IMAGE_DATA_H

// LOVE
#include <common/Data.h>
#include <filesystem/File.h>

namespace love
{	
namespace image
{
	// Pixel format structure. 
	struct pixel 
	{
		// Red, green, blue, alpha.
		unsigned char r, g, b, a;
	};

	/**
	* Represents raw pixel data. 
	**/
	class ImageData : public Data
	{
	public:
		
		enum Format
		{
			FORMAT_TGA = 1,
			FORMAT_BMP,
			FORMAT_GIF,
			FORMAT_JPG,
			FORMAT_PNG,
			FORMAT_MAX_ENUM
		};

		/**
		* Destructor.
		**/
		virtual ~ImageData(){};
		
		static bool getConstant(const char * in, Format & out);
		static bool getConstant(Format in, const char *& out);

		/**
		* Paste part of one ImageData onto another. The subregion defined by the top-left
		* corner (sx, sy) and the size (sw,sh) will be pasted to (dx,dy) in this ImageData.
		* @param dx The destination x-coordinate.
		* @param dy The destination y-coordinate.
		* @param sx The source x-coordinate.
		* @param sy The source y-coordinate.
		* @param sw The source width.
		* @param sh The source height.
		**/
		void paste(ImageData * src, int dx, int dy, int sx, int sy, int sw, int sh);

		/**
		* Checks whether a position is inside this ImageData. Useful for checking bounds.
		* @param x The position along the x-axis. 
		* @param y The position along the y-axis.
		**/
		bool inside(int x, int y) const;

		/**
		* Gets the width of this ImageData.
		* @return The width of this ImageData.
		**/
		virtual int getWidth() const = 0;

		/**
		* Gets the height of this ImageData.
		* @return The height of this ImageData.
		**/
		virtual int getHeight() const  = 0;

		/**
		* Sets the pixel at location (x,y). No effect if out of bounds.
		* @param x The location along the x-axis. 
		* @param y The location along the y-axis.
		* @param p The color to use for the given location.
		**/
		virtual void setPixel(int x, int y, pixel p) = 0;

		/**
		* Gets the pixel at location (x,y). Returns black (0,0,0,0) if out
		* out of bounds.
		* @param x The location along the x-axis. 
		* @param y The location along the y-axis.
		* @return The color for the given location.
		**/
		virtual pixel getPixel(int x, int y) = 0;
		
		/**
		 * Encodes raw pixel data into a given format.
		 * @param f The format to convert to.
		 * @return A pointer to the encoded image data.
		 **/
		virtual void encode(love::filesystem::File * f, Format format) = 0;
		
	private:
		static StringMap<Format, FORMAT_MAX_ENUM>::Entry formatEntries[];
		static StringMap<Format, FORMAT_MAX_ENUM> formats;

	}; // ImageData

} // image
} // love

#endif // LOVE_IMAGE_IMAGE_DATA_H
