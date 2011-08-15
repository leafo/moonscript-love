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

#ifndef LOVE_GRAPHICS_OPENGL_IMAGE_H
#define LOVE_GRAPHICS_OPENGL_IMAGE_H

// LOVE
#include <common/Matrix.h>
#include <common/math.h>
#include <common/config.h>
#include <image/ImageData.h>
#include <graphics/Image.h>
#include "Quad.h"

// OpenGL
#include "GLee.h"
#include <SDL/SDL_opengl.h>

namespace love
{
namespace graphics
{
namespace opengl
{

	/**
	* A drawable image based on OpenGL-textures. This class takes ImageData
	* objects and create textures on the GPU for fast drawing.
	*
	* @author Anders Ruud
	**/
	class Image : public love::graphics::Image
	{
	private:

		// The ImageData from which the texture is created.
		love::image::ImageData * data;

		// Width and height of the hardware texture.
		float width, height;

		// OpenGL texture identifier.
		GLuint texture;

		// The source vertices of the image.
		vertex vertices[4];

		// The settings we need to save when reloading.
		struct
		{
			Image::Filter filter;
			Image::Wrap wrap;
		} settings;

		bool loadVolatilePOT();
		bool loadVolatileNPOT();

	public:

		/**
		* Creates a new Image. Not that anything is ready to use
		* before load is called.
		*
		* @param file The file from which to load the image.
		**/
		Image(love::image::ImageData * data);

		/**
		* Destructor. Deletes the hardware texture and other resources.
		**/
		virtual ~Image();

		float getWidth() const;
		float getHeight() const;

		const vertex * getVertices() const;

		love::image::ImageData * getData() const;

		/**
		* Generate vertices according to a subimage.
		*
		* Note: out-of-range values will be clamped.
		* Note: the vertex colors will not be changed.
		*
		* @param x The top-left corner of the subimage along the x-axis.
		* @param y The top-left corner of the subimage along the y-axis.
		* @param w The width of the subimage.
		* @param h The height of the subimage.
		* @param vertices A vertex array of size four.
		**/
		void getRectangleVertices(int x, int y, int w, int h, vertex * vertices) const;

		/**
		* @copydoc Drawable::draw()
		**/
		void draw(float x, float y, float angle, float sx, float sy, float ox, float oy, float kx, float ky) const;

		/**
		* This function draws a section of the image using a Quad object.
		*
		* @copydetails Image::draws()
		* @param frame Represents the region of the Image to draw.
		**/
		void drawq(Quad * quad, float x, float y, float angle, float sx, float sy, float ox, float oy, float kx, float ky) const;

		/**
		* Sets the filter mode.
		*
		* @param mode The filter mode.
		**/
		void setFilter(Image::Filter f);

		Image::Filter getFilter() const;

		void setWrap(Image::Wrap r);

		Image::Wrap getWrap() const;

		void bind() const;

		bool load();
		void unload();

		// Implements Volatile.
		bool loadVolatile();
		void unloadVolatile();

	private:

		void drawv(const Matrix & t, const vertex * v) const;

		friend class PixelEffect;
		GLuint getTextureName() const { return texture; }

	}; // Image

} // opengl
} // graphics
} // love

#endif // LOVE_GRAPHICS_OPENGL_IMAGE_H
