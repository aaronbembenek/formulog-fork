#include "functors.h"
#include "funcs.hpp"

using namespace flg;
using namespace std;

souffle::RamDomain
nth(souffle::SymbolTable *st, souffle::RecordTable *rt, souffle::RamDomain n, souffle::RamDomain ref,
    souffle::RamDomain arity) {
    /*
    if (ref == 0) {
        return 0;
    }
     */
    assert(ref && arity);
    return Term::unintize(ref)->as_complex().val[n]->intize();
    /*
    auto tup = rt->unpack(ref, arity);
    return tup[n];
     */
}

/* INSERT 0 */