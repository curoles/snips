
SRC:=$(TEST_DIR)/test.cpp
uLISP_INC_DIR:=$(TEST_DIR)/../..
uLISP_BUILD_DIR:=$(BUILD_DIR)/../../ulisp
uLISP_LIB := $(uLISP_BUILD_DIR)/libulisp.a

$(BUILD_DIR)/test: $(SRC) $(uLISP_LIB) $(TEST_DIR)/../test.cpp
	g++ $(SRC) -I$(uLISP_INC_DIR) -Wl,--library=:$(uLISP_LIB) -o $@

