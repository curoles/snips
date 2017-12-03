#pragma once

#include "cgem/logging.h"

typedef logging::Logger<3> Log;

Log& get_logger();

enum {ERR=0, WRN, INFO, DBG};
