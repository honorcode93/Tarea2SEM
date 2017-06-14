DIR=/usr/local
LIBS= \
   -lgecodeflatzinc  -lgecodedriver \
   -lgecodegist      -lgecodesearch \
   -lgecodeminimodel -lgecodeset    \
   -lgecodefloat     -lgecodeint    \
   -lgecodekernel    -lgecodesupport \

shop: openshop.cpp
	g++ -Wall -I$(DIR)/include -c openshop.cpp
	g++ -Wall -L$(DIR)/lib -o openshop openshop.o $(LIBS)

