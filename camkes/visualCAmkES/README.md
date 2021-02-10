<!--
     Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# VisualCAmkES

For detailed information how to install and use visualCAmkES, read the wiki page: https://docs.sel4.systems/VisualCAmkES/

## Installing dependenices
On top of the dependenices required for camkes-tool, visualCAmkES requires are few other installations such as Qt and Graphviz.

### Install Qt
#### Debian / Ubuntu / (Possibly other linux distros with different package managers)
```
sudo apt-get install python-pyqt5
sudo apt-get install python-pyqt5.qtsvg
```
#### From source (for Macs and all linux distros, and possibly windows)
##### Installing Qt libraries
```
git clone git://code.qt.io/qt/qt5.git
cd qt5
git checkout 5.5

./init-repository --no-webkit --module-subset=qtbase,qtsvg

# Check where Qt will install - needed for PyQt5
./configure --help
# Have a look at where qt will be installed, for me it was installed in /usr/local/Qt-5.5.1
./configure -release -nomake examples -nomake tests -opensource -confirm-license  # add "-qt-xcb" for linux

make -j4 # This takes a long time (1-3 hrs)
make install
```

##### Installing sip
```
curl -O http://liquidtelecom.dl.sourceforge.net/project/pyqt/sip/sip-4.17/sip-4.17.tar.gz
tar -xvf sip-4.17.tar.gz
cd sip-4.17

python configure.py

make -j4
make install
```

##### Installing PyQt5
```
curl -O http://liquidtelecom.dl.sourceforge.net/project/pyqt/PyQt5/PyQt-5.5.1/PyQt-gpl-5.5.1.tar.gz
tar -xvf PyQt-gpl-5.5.1.tar.gz
cd PyQt-gpl-5.5.1

# -q option specifies where qmake is installed. You know where it was installed from "Downloading and Installing Qt" step.
python configure.py --no-tools --no-designer-plugin --no-qml-plugin -q /usr/local/Qt-5.5.1/bin/qmake -w --confirm-license

make -j4 # This also takes a while, 1-3 hrs depending on computer
make install
```

### Install Graphviz
#### Debian / Ubuntu / (Possibly other linux distros with different package managers)
```
sudo apt-get install graphviz
pip install --user graphviz
pip install --user pydotplus
```
#### For macs
For macs, to install graphviz (first step above), visit this website: http://www.ryandesign.com/graphviz/ , download the latest development (or stable as long as greater than version 16), and install the dmg. Pip will work on the mac.

### Installing other python dependies
```
pip install --user ansi2html
```

## How to use
Very simple:
```
python [path/to/camkes-tool/camkes]/visualCAmkES
```
