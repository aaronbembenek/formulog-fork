#pragma once

#include <chrono>
#include <souffle/SouffleInterface.h>
#include <tbb/combinable.h>
#include <omp.h>
#include "ConcurrentHashMap.hpp"
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

inline struct SmtStatsHolder {
    ConcurrentHashMap<int, SmtStats> memo;

    SmtStats &local() {
        return memo[omp_get_thread_num()];
    }

    template<typename F>
    void combine_each(F func) {
        for (auto &e : memo) {
            func(e.second);
        }
    }
} smt_data;

}