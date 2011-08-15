#ifndef LOVE_GRAPHICS_EFFECT_H
#define LOVE_GRAPHICS_EFFECT_H

#include <common/Object.h>
#include <string>
#include <map>
#include "Image.h"
#include "Canvas.h"

namespace love
{
namespace graphics
{
namespace opengl
{
	// A fragment shader
	class PixelEffect : public Volatile // Volatile?
	{
	public:
		PixelEffect(const std::string& code);
		virtual ~PixelEffect();
		std::string getWarnings() const;

		virtual bool loadVolatile();
		virtual void unloadVolatile();

		void attach();
		static void detach();
		static bool isSupported();

		void sendFloat(const std::string& name, int count, const GLfloat* vec);
		void sendMatrix(const std::string& name, int size, const GLfloat* m);
		void sendImage(const std::string& name, const Image& image);
		void sendCanvas(const std::string& name, const Canvas& canvas);

	private:
		GLint getUniformLocation(const std::string& name);
		void checkSetUniformError();
		GLuint _program;
		std::string _code; // volatile and stuff

		// texture unit pool for setting images
		static std::map<std::string, GLint> _texture_unit_pool;
		static GLint _current_texture_unit;
		static GLint _max_texture_units;
		static GLint getTextureUnit(const std::string& name);
	};

} // opengl
} // graphics
} // love

#endif // LOVE_GRAPHICS_EFFECT_H
