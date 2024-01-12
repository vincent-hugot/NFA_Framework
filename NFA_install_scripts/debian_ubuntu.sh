

sudo apt install git graphviz pdftk python3-lark fonts-linuxlibertine \
  python3-pylsp idle

# get my framework, then run tests
git clone https://github.com/vincent-hugot/NFA_Framework.git
cd NFA_Framework/ || return
./tests.py
xdg-open visu.pdf