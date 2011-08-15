LÖVE is an *awesome* framework you can use to make 2D games in Lua. It's free, open-source, and works on Windows, Mac OS X and Linux.

Documentation
-------------

We use our [wiki][wiki] for documentation.
If you need further help, feel free to ask on our [forums][forums], and last but not least there's the irc channel [#love on Freenode][irc].

Compilation
-----------

###Windows
Use the project files for Visual C++ 2008 or 2010 (2010 preferred) located in the platform dir.

###*nix
Run platform/unix/automagic, then run ./configure and make.

###OSX
Use the XCode project in platform/macosx.

For both Windows and OSX there are dependencies available [here][dependencies].

Repository information
----------------------

We use the 'default' branch for development, and therefore it should not be considered stable.
Also used is the 'minor' branch, which is used for features in the next minor version and it is
not our development target (which would be the next revision). (Version numbers formatted major.minor.revision.)

We tag all our releases (since we started using mercurial), and have binary downloads available for them.

Builds
------

Releases are found in the 'downloads' section on bitbucket, are linked on [the site][site],
and there's a ppa for ubuntu, [ppa:bartbes/love-stable][stableppa].

There are also unstable/nightly builds:

- For windows they are located [here][winbuilds].
- For ubuntu linux they are in [ppa:bartbes/love-unstable][unstableppa]
- For arch linux there's [love-hg][aur] in the AUR.
- For other linuxes and OSX there are currently no official builds.

Dependencies
------------

- SDL
- OpenGL
- OpenAL
- Lua / LuaJIT / LLVM-lua
- DevIL with MNG and TIFF
- FreeType
- PhysicsFS
- ModPlug
- mpg123
- Vorbisfile

[site]: http://love2d.org
[wiki]: http://love2d.org/wiki
[forums]: http://love2d.org/forums
[irc]: irc://irc.freenode.net/love
[dependencies]: http://love2d.org/sdk
[winbuilds]: http://love2d.org/builds
[stableppa]: https://launchpad.net/~bartbes/+archive/love-stable
[unstableppa]: https://launchpad.net/~bartbes/+archive/love-unstable
[aur]: http://aur.archlinux.org/packages.php?ID=35279
