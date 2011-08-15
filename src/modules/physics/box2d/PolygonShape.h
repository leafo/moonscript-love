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

#ifndef LOVE_PHYSICS_BOX2D_POLYGON_SHAPE_H
#define LOVE_PHYSICS_BOX2D_POLYGON_SHAPE_H

// Module
#include "Shape.h"

namespace love
{
namespace physics
{
namespace box2d
{
	/**
	* You should know what a Polygon is. :)
	* 
	* This class is needed so that we can easily get
	* the transformed points in Lua. By calling shape:getPoints(), 
	* the result can be passed directly to love.graphics.polygon().
	**/
	class PolygonShape : public Shape
	{
	public:

		/**
		* Create a new PolygonShape from the parent Body and
		* a Box2D polygon definition.
		* @param body The parent Body. 
		* @param def The polygon definition.
		**/
		PolygonShape(Body * body, b2PolygonDef * def);

		virtual ~PolygonShape();

		/**
		* Returns the transformed points of the polygon.
		* This function is useful for debug drawing and such.
		*
		* The result can be directly passed into love.graphics.polygon().
		**/
		int getPoints(lua_State * L);
	};

} // box2d
} // physics
} // love

#endif // LOVE_PHYSICS_BOX2D_POLYGON_SHAPE_H
