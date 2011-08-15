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

#include "SpriteBatch.h"

// STD
#include <iostream>

// LOVE
#include "Image.h"
#include "Quad.h"
#include "VertexBuffer.h"

namespace love
{
namespace graphics
{
namespace opengl
{
	SpriteBatch::SpriteBatch(Image * image, int size, int usage)
		: image(image)
		, size(size)
		, next(0)
		, color(0)
		, array_buf(0)
		, element_buf(0)
	{
		image->retain();

		GLenum gl_usage;

		switch (usage)
		{
		default:
		case USAGE_DYNAMIC:
			gl_usage = GL_DYNAMIC_DRAW;
			break;
		case USAGE_STATIC:
			gl_usage = GL_STATIC_DRAW;
			break;
		case USAGE_STREAM:
			gl_usage = GL_STREAM_DRAW;
			break;
		}

		int vertex_size = sizeof(vertex) * 4 * size;
		int element_size = sizeof(GLushort) * 6 * size;

		array_buf = VertexArray::Create(vertex_size, GL_ARRAY_BUFFER, gl_usage);
		element_buf = VertexArray::Create(element_size, GL_ELEMENT_ARRAY_BUFFER, GL_STATIC_DRAW);

		// Fill element buffer.
		{
			VertexBuffer::Bind bind(*element_buf);

			GLushort *indices = static_cast<GLushort*>(element_buf->map(GL_WRITE_ONLY));

			if (indices)
			{
				for (int i = 0; i < size; ++i)
				{
					indices[i*6+0] = 0+(i*4);
					indices[i*6+1] = 1+(i*4);
					indices[i*6+2] = 2+(i*4);

					indices[i*6+3] = 0+(i*4);
					indices[i*6+4] = 2+(i*4);
					indices[i*6+5] = 3+(i*4);
				}
			}

			element_buf->unmap();
		}
	}

	SpriteBatch::~SpriteBatch()
	{
		image->release();

		delete color;
		delete array_buf;
		delete element_buf;
	}

	void SpriteBatch::add(float x, float y, float a, float sx, float sy, float ox, float oy, float kx, float ky)
	{
		// Only do this if there's a free slot.
		if(next < size)
		{
			// Needed for texture coordinates.
			memcpy(sprite, image->getVertices(), sizeof(vertex)*4);

			// Transform.
			Matrix t;
			t.setTransformation(x, y, a, sx, sy, ox, oy, kx, ky);
			t.transform(sprite, sprite, 4);

			if (color)
				setColorv(sprite, *color);

			addv(sprite);

			// Increment counter.
			next++;
		}
	}

	void SpriteBatch::addq(Quad * quad, float x, float y, float a, float sx, float sy, float ox, float oy, float kx, float ky)
	{
		// Only do this if there's a free slot.
		if(next < size)
		{
			// Needed for colors.
			memcpy(sprite, quad->getVertices(), sizeof(vertex)*4);

			// Transform.
			Matrix t;
			t.setTransformation(x, y, a, sx, sy, ox, oy, kx, ky);
			t.transform(sprite, sprite, 4);

			if (color)
				setColorv(sprite, *color);

			addv(sprite);

			// Increment counter.
			next++;
		}
	}

	void SpriteBatch::clear()
	{
		// Reset the position of the next index.
		next = 0;
	}

	void * SpriteBatch::lock()
	{
		VertexArray::Bind bind(*array_buf);

		return array_buf->map(GL_READ_WRITE);
	}

	void SpriteBatch::unlock()
	{
		VertexArray::Bind bind(*array_buf);

		array_buf->unmap();
	}

	void SpriteBatch::setImage(Image * newimage)
	{
		image->release();
		image = newimage;
		image->retain();
	}

	void SpriteBatch::setColor(const Color & color)
	{
		if(!this->color)
			this->color = new Color(color);
		else
			*(this->color) = color;
	}

	void SpriteBatch::setColor()
	{
		delete color;
		color = 0;
	}

	void SpriteBatch::draw(float x, float y, float angle, float sx, float sy, float ox, float oy, float kx, float ky) const
	{
		const int color_offset = 0;
		const int vertex_offset = sizeof(unsigned char) * 4;
		const int texel_offset = sizeof(unsigned char) * 4 + sizeof(float) * 2;

		static Matrix t;

		glPushMatrix();

		t.setTransformation(x, y, angle, sx, sy, ox, oy, kx, ky);
		glMultMatrixf((const GLfloat*)t.getElements());

		image->bind();

		VertexBuffer::Bind array_bind(*array_buf);
		VertexBuffer::Bind element_bind(*element_buf);

		// Apply per-sprite color, if a color is set.
		if (color)
		{
			glEnableClientState(GL_COLOR_ARRAY);
			glColorPointer(4, GL_UNSIGNED_BYTE, sizeof(vertex), array_buf->getPointer(color_offset));
		}

		glEnableClientState(GL_VERTEX_ARRAY);
		glVertexPointer(2, GL_FLOAT, sizeof(vertex), array_buf->getPointer(vertex_offset));

		glEnableClientState(GL_TEXTURE_COORD_ARRAY);
		glTexCoordPointer(2, GL_FLOAT, sizeof(vertex), array_buf->getPointer(texel_offset));

		glDrawElements(GL_TRIANGLES, next*6, GL_UNSIGNED_SHORT, element_buf->getPointer(0));

		glDisableClientState(GL_VERTEX_ARRAY);
		glDisableClientState(GL_TEXTURE_COORD_ARRAY);
		glDisableClientState(GL_COLOR_ARRAY);

		glPopMatrix();
	}

	void SpriteBatch::addv(const vertex * v)
	{
		int sprite_size = sizeof(vertex) * 4;

		VertexArray::Bind bind(*array_buf);

		array_buf->fill(next * sprite_size, sprite_size, v);
	}

	void SpriteBatch::setColorv(vertex * v, const Color & color)
	{
		v[0].r = color.r; v[0].g = color.g; v[0].b = color.b; v[0].a = color.a;
		v[1].r = color.r; v[1].g = color.g; v[1].b = color.b; v[1].a = color.a;
		v[2].r = color.r; v[2].g = color.g; v[2].b = color.b; v[2].a = color.a;
		v[3].r = color.r; v[3].g = color.g; v[3].b = color.b; v[3].a = color.a;
	}

} // opengl
} // graphics
} // love
