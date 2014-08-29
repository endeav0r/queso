queso
=====

queso is a cheese-based salsa which goes well with nacho chips.

build
=====

sometimes i build in windows with cygwin, sometimes in debian.

build/make/install SDL2.0, SDL ttf 2.whatever, lua5.2, udis86 (from github, i think http://github.com/vmt/udis86)

don't use the makefiles. makefiles are stupid and for people who want to learn about autotools

use build.py. build.py is awesome and is for people who are lazy.

python build.py (this will just build)
python build.py build linux (changes stuff up to work wel with linux)
python build.by clean (uh, yeah, make clean)
