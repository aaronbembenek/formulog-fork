#pragma once

#include <chrono>
#include <souffle/SouffleInterface.h>
#include <tbb/combinable.h>
#include "smt_solver.h"

namespace flg::globals {

inline souffle::SouffleProgram *program{nullptr};

inline smt::SmtSolverMode smt_solver_mode{smt::SmtSolverMode::check_sat_assuming};

inline bool smt_double_check{true};

inline size_t smt_cache_size{100};

inline bool smt_stats{false};

typedef std::chrono::duration<double, std::milli> time_t;

struct SmtStats {
    std::vector<time_t> smt_calls;
    unsigned smt_cache_clears;
};

inline tbb::combinable<SmtStats> smt_data;

}