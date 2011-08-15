
#include "lpeg.h"

extern "C" {
#include "liblpeg/lpeg.h"
extern int luaopen_lpeg(lua_State *L);
}

namespace love
{
namespace lpeg
{

int __open(lua_State *l) {
	luaopen_lpeg(l);
}

}
}
