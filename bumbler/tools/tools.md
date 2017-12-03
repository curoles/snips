# GNU Prolog

```
cd path/tools
mkdir gprolog
cd gprolog
wget http://www.gprolog.org/gprolog-1.4.4.tar.gz
gvim gprolog-1.4.4/INSTALL 
cd gprolog-1.4.4/src
./configure --prefix=/local_disk/igor/tools/gprolog/gprolog-1.4.4/install
make
make install
make check
cd ..
ls install/bin/
```
