#include <array>
#include <limits>
#include <stack>
#include <type_traits>
#include <utility>

#include "Term.hpp"

namespace flg {

template <typename T>
int BaseTerm<T>::compare(const BaseTerm<T>& t1, const BaseTerm<T>& t2) {
  return (t1.val > t2.val) - (t1.val < t2.val);
}

// Specializations for BaseTerm<float> and BaseTerm<double>
// This creates a total order where NaNs compare after everything else, avoiding
// undefined behavior when calling std::sort() in natural order.

template <>
int BaseTerm<float>::compare(
  const BaseTerm<float>& t1, const BaseTerm<float>& t2
) {
  if (isunordered(t1.val, t2.val)) {
    return isnan(t1.val) - isnan(t2.val);
  }
  return (t1.val > t2.val) - (t1.val < t2.val);
}

template <>
int BaseTerm<double>::compare(
  const BaseTerm<double>& t1, const BaseTerm<double>& t2
) {
  if (isunordered(t1.val, t2.val)) {
    return isnan(t1.val) - isnan(t2.val);
  }
  return (t1.val > t2.val) - (t1.val < t2.val);
}

ostream &operator<<(ostream &out, const Term &t) {
    switch (t.sym) {
        case Symbol::boxed_bool: {
            return out << boolalpha << t.as_base<bool>().val << noboolalpha;
        }
        case Symbol::boxed_i32: {
            return out << t.as_base<int32_t>().val;
        }
        case Symbol::boxed_i64: {
            return out << t.as_base<int64_t>().val << "L";
        }
        case Symbol::boxed_fp32: {
            auto val = t.as_base<float>().val;
            if (isnan(val)) {
                out << "fp32_nan";
            } else if (isinf(val)) {
                if (val > 0) {
                    out << "fp32_pos_infinity";
                } else {
                    out << "fp32_neg_infinity";
                }
            } else {
                out << val << "F";
            }
            return out;
        }
        case Symbol::boxed_fp64: {
            auto val = t.as_base<double>().val;
            if (isnan(val)) {
                out << "fp64_nan";
            } else if (isinf(val)) {
        if (val > 0) {
          out << "fp64_pos_infinity";
        } else {
          out << "fp64_neg_infinity";
        }
      } else {
        out << val << "F";
      }
      return out;
    }
    case Symbol::boxed_string: {
      return out << "\"" << t.as_base<string>().val << "\"";
    }
    default: {
      auto& x = t.as_complex();
      out << x.sym;
      size_t n = x.arity;
      if (n > 0) {
        out << "(";
        for (size_t i = 0; i < n; ++i) {
          out << *x.val[i];
          if (i < n - 1) {
            out << ", ";
          }
        }
        out << ")";
      }
      return out;
    }
  }
}

/*
int Term::compare_natural(Term* t1, Term* t2) {
  stack<pair<Term*, Term*>> w;
  w.emplace(t1, t2);
  while (!w.empty()) {
    auto p = w.top();
    w.pop();
    t1 = p.first;
    t2 = p.second;
    if (t1 == t2) {
      continue;
    }
    if (t1->sym < t2->sym) {
      return -1;
    }
    if (t1->sym > t2->sym) {
      return 1;
    }
    switch (t1->sym) {
      case Symbol::boxed_bool: {
        auto& x = t1->as_base<bool>();
        auto& y = t2->as_base<bool>();
        int cmp = BaseTerm<bool>::compare(x, y);
        if (cmp != 0) {
          return cmp;
        }
        break;
      }
      case Symbol::boxed_i32: {
        auto& x = t1->as_base<int32_t>();
        auto& y = t2->as_base<int32_t>();
        int cmp = BaseTerm<int32_t>::compare(x, y);
        if (cmp != 0) {
          return cmp;
        }
        break;
      }
      case Symbol::boxed_i64: {
        auto& x = t1->as_base<int64_t>();
        auto& y = t2->as_base<int64_t>();
        int cmp = BaseTerm<int64_t>::compare(x, y);
        if (cmp != 0) {
          return cmp;
        }
        break;
      }
      case Symbol::boxed_fp32: {
        auto& x = t1->as_base<float>();
        auto& y = t2->as_base<float>();
        int cmp = BaseTerm<float>::compare(x, y);
        if (cmp != 0) {
          return cmp;
        }
        break;
      }
      case Symbol::boxed_fp64: {
        auto& x = t1->as_base<double>();
        auto& y = t2->as_base<double>();
        int cmp = BaseTerm<double>::compare(x, y);
        if (cmp != 0) {
          return cmp;
        }
        break;
      }
      case Symbol::boxed_string: {
        auto& x = t1->as_base<string>();
        auto& y = t2->as_base<string>();
        int cmp = BaseTerm<string>::compare(x, y);
        if (cmp != 0) {
          return cmp;
        }
        break;
      }
      default: {
        auto& x = t1->as_complex();
        auto& y = t2->as_complex();
        size_t n = x.arity;
        for (size_t i = 0; i < n; ++i) {
          w.emplace(x.val[i], y.val[i]);
        }
      }
    }
  }
  return 0;
}
 */

// Template hash function for arrays of term_ptr's
template <size_t N>
struct ComplexTermHash {
  typedef array<term_ptr, N> key_type;

  size_t operator()(const key_type& arr) const {
    size_t retval = 0;
    for (term_ptr p : arr) {
      retval ^=
        (retval << 32) + 0xdeadbeef + reinterpret_cast<size_t>(p) / sizeof(p);
    }
    return retval;
  }
};

// Concurrency-safe cache for ComplexTerm values
template <Symbol S> class ComplexTermCache {
  inline static constexpr size_t arity = symbol_arity(S);
  typedef concurrent_unordered_map<
    array<term_ptr, arity>, term_ptr, ComplexTermHash<arity>> map_t;
  inline static map_t cache;

  public:
  template <typename... T,
            typename = enable_if_t<sizeof...(T) == arity>>
  static term_ptr get(T... val) {
      array<term_ptr, arity> arr = {val...};
      auto it = cache.find(arr);
      if (it != cache.end()) {
          return it->second;
      }
      auto *heap_arr = new term_ptr[arity]{val...};
      auto ptr = new ComplexTerm(S, arity, heap_arr);
      auto result = cache.emplace(arr, ptr);
      if (!result.second) {
          // Term was not successfully inserted
          delete ptr;
      }
      return result.first->second;
  }
};

template<Symbol S, typename... T>
term_ptr Term::make(T... val) {
    return ComplexTermCache<S>::get(val...);
}

/* INSERT 0 */

term_ptr ComplexTerm::fresh_smt_var() {
#ifdef FLG_DEV
    return nullptr;
#else
    return new ComplexTerm(Symbol::smt_var__bool__bool, 0, nullptr);
#endif
}

term_ptr Term::make_generic(Symbol sym, const vector<term_ptr> &terms) {
    if (symbol_arity(sym) != terms.size()) {
        string message = "Expected arity ";
        message += to_string(symbol_arity(sym));
        message += " for symbol (ID ";
        message += to_string(static_cast<int>(sym));
        message += "), got arity ";
        message += to_string(terms.size());
        throw std::runtime_error(message);
    }
    switch (sym) {
/* INSERT 1 */
        default:
            throw std::runtime_error(
                    "Invalid symbol (ID " +
                    to_string(static_cast<int>(sym)) +
                    ") used to construct term"
            );
    }
}

const BaseTerm<int32_t> Term::i32_memo[201] = {
        {Symbol::boxed_i32, -100},
        {Symbol::boxed_i32, -99},
        {Symbol::boxed_i32, -98},
        {Symbol::boxed_i32, -97},
        {Symbol::boxed_i32, -96},
        {Symbol::boxed_i32, -95},
        {Symbol::boxed_i32, -94},
        {Symbol::boxed_i32, -93},
        {Symbol::boxed_i32, -92},
        {Symbol::boxed_i32, -91},
        {Symbol::boxed_i32, -90},
        {Symbol::boxed_i32, -89},
        {Symbol::boxed_i32, -88},
        {Symbol::boxed_i32, -87},
        {Symbol::boxed_i32, -86},
        {Symbol::boxed_i32, -85},
        {Symbol::boxed_i32, -84},
        {Symbol::boxed_i32, -83},
        {Symbol::boxed_i32, -82},
        {Symbol::boxed_i32, -81},
        {Symbol::boxed_i32, -80},
        {Symbol::boxed_i32, -79},
        {Symbol::boxed_i32, -78},
        {Symbol::boxed_i32, -77},
        {Symbol::boxed_i32, -76},
        {Symbol::boxed_i32, -75},
        {Symbol::boxed_i32, -74},
        {Symbol::boxed_i32, -73},
        {Symbol::boxed_i32, -72},
        {Symbol::boxed_i32, -71},
        {Symbol::boxed_i32, -70},
        {Symbol::boxed_i32, -69},
        {Symbol::boxed_i32, -68},
        {Symbol::boxed_i32, -67},
        {Symbol::boxed_i32, -66},
        {Symbol::boxed_i32, -65},
        {Symbol::boxed_i32, -64},
        {Symbol::boxed_i32, -63},
        {Symbol::boxed_i32, -62},
        {Symbol::boxed_i32, -61},
        {Symbol::boxed_i32, -60},
        {Symbol::boxed_i32, -59},
        {Symbol::boxed_i32, -58},
        {Symbol::boxed_i32, -57},
        {Symbol::boxed_i32, -56},
        {Symbol::boxed_i32, -55},
        {Symbol::boxed_i32, -54},
        {Symbol::boxed_i32, -53},
        {Symbol::boxed_i32, -52},
        {Symbol::boxed_i32, -51},
        {Symbol::boxed_i32, -50},
        {Symbol::boxed_i32, -49},
        {Symbol::boxed_i32, -48},
        {Symbol::boxed_i32, -47},
        {Symbol::boxed_i32, -46},
        {Symbol::boxed_i32, -45},
        {Symbol::boxed_i32, -44},
        {Symbol::boxed_i32, -43},
        {Symbol::boxed_i32, -42},
        {Symbol::boxed_i32, -41},
        {Symbol::boxed_i32, -40},
        {Symbol::boxed_i32, -39},
        {Symbol::boxed_i32, -38},
        {Symbol::boxed_i32, -37},
        {Symbol::boxed_i32, -36},
        {Symbol::boxed_i32, -35},
        {Symbol::boxed_i32, -34},
        {Symbol::boxed_i32, -33},
        {Symbol::boxed_i32, -32},
        {Symbol::boxed_i32, -31},
        {Symbol::boxed_i32, -30},
        {Symbol::boxed_i32, -29},
        {Symbol::boxed_i32, -28},
        {Symbol::boxed_i32, -27},
        {Symbol::boxed_i32, -26},
        {Symbol::boxed_i32, -25},
        {Symbol::boxed_i32, -24},
        {Symbol::boxed_i32, -23},
        {Symbol::boxed_i32, -22},
        {Symbol::boxed_i32, -21},
        {Symbol::boxed_i32, -20},
        {Symbol::boxed_i32, -19},
        {Symbol::boxed_i32, -18},
        {Symbol::boxed_i32, -17},
        {Symbol::boxed_i32, -16},
        {Symbol::boxed_i32, -15},
        {Symbol::boxed_i32, -14},
        {Symbol::boxed_i32, -13},
        {Symbol::boxed_i32, -12},
        {Symbol::boxed_i32, -11},
        {Symbol::boxed_i32, -10},
        {Symbol::boxed_i32, -9},
        {Symbol::boxed_i32, -8},
        {Symbol::boxed_i32, -7},
        {Symbol::boxed_i32, -6},
        {Symbol::boxed_i32, -5},
        {Symbol::boxed_i32, -4},
        {Symbol::boxed_i32, -3},
        {Symbol::boxed_i32, -2},
        {Symbol::boxed_i32, -1},
        {Symbol::boxed_i32, 0},
        {Symbol::boxed_i32, 1},
        {Symbol::boxed_i32, 2},
        {Symbol::boxed_i32, 3},
        {Symbol::boxed_i32, 4},
        {Symbol::boxed_i32, 5},
        {Symbol::boxed_i32, 6},
        {Symbol::boxed_i32, 7},
        {Symbol::boxed_i32, 8},
        {Symbol::boxed_i32, 9},
        {Symbol::boxed_i32, 10},
        {Symbol::boxed_i32, 11},
        {Symbol::boxed_i32, 12},
        {Symbol::boxed_i32, 13},
        {Symbol::boxed_i32, 14},
        {Symbol::boxed_i32, 15},
        {Symbol::boxed_i32, 16},
        {Symbol::boxed_i32, 17},
        {Symbol::boxed_i32, 18},
        {Symbol::boxed_i32, 19},
        {Symbol::boxed_i32, 20},
        {Symbol::boxed_i32, 21},
        {Symbol::boxed_i32, 22},
        {Symbol::boxed_i32, 23},
        {Symbol::boxed_i32, 24},
        {Symbol::boxed_i32, 25},
        {Symbol::boxed_i32, 26},
        {Symbol::boxed_i32, 27},
        {Symbol::boxed_i32, 28},
        {Symbol::boxed_i32, 29},
        {Symbol::boxed_i32, 30},
        {Symbol::boxed_i32, 31},
        {Symbol::boxed_i32, 32},
        {Symbol::boxed_i32, 33},
        {Symbol::boxed_i32, 34},
        {Symbol::boxed_i32, 35},
        {Symbol::boxed_i32, 36},
        {Symbol::boxed_i32, 37},
        {Symbol::boxed_i32, 38},
        {Symbol::boxed_i32, 39},
        {Symbol::boxed_i32, 40},
        {Symbol::boxed_i32, 41},
        {Symbol::boxed_i32, 42},
        {Symbol::boxed_i32, 43},
        {Symbol::boxed_i32, 44},
        {Symbol::boxed_i32, 45},
        {Symbol::boxed_i32, 46},
        {Symbol::boxed_i32, 47},
        {Symbol::boxed_i32, 48},
        {Symbol::boxed_i32, 49},
        {Symbol::boxed_i32, 50},
        {Symbol::boxed_i32, 51},
        {Symbol::boxed_i32, 52},
        {Symbol::boxed_i32, 53},
        {Symbol::boxed_i32, 54},
        {Symbol::boxed_i32, 55},
        {Symbol::boxed_i32, 56},
        {Symbol::boxed_i32, 57},
        {Symbol::boxed_i32, 58},
        {Symbol::boxed_i32, 59},
        {Symbol::boxed_i32, 60},
        {Symbol::boxed_i32, 61},
        {Symbol::boxed_i32, 62},
        {Symbol::boxed_i32, 63},
        {Symbol::boxed_i32, 64},
        {Symbol::boxed_i32, 65},
        {Symbol::boxed_i32, 66},
        {Symbol::boxed_i32, 67},
        {Symbol::boxed_i32, 68},
        {Symbol::boxed_i32, 69},
        {Symbol::boxed_i32, 70},
        {Symbol::boxed_i32, 71},
        {Symbol::boxed_i32, 72},
        {Symbol::boxed_i32, 73},
        {Symbol::boxed_i32, 74},
        {Symbol::boxed_i32, 75},
        {Symbol::boxed_i32, 76},
        {Symbol::boxed_i32, 77},
        {Symbol::boxed_i32, 78},
        {Symbol::boxed_i32, 79},
        {Symbol::boxed_i32, 80},
        {Symbol::boxed_i32, 81},
        {Symbol::boxed_i32, 82},
        {Symbol::boxed_i32, 83},
        {Symbol::boxed_i32, 84},
        {Symbol::boxed_i32, 85},
        {Symbol::boxed_i32, 86},
        {Symbol::boxed_i32, 87},
        {Symbol::boxed_i32, 88},
        {Symbol::boxed_i32, 89},
        {Symbol::boxed_i32, 90},
        {Symbol::boxed_i32, 91},
        {Symbol::boxed_i32, 92},
        {Symbol::boxed_i32, 93},
        {Symbol::boxed_i32, 94},
        {Symbol::boxed_i32, 95},
        {Symbol::boxed_i32, 96},
        {Symbol::boxed_i32, 97},
        {Symbol::boxed_i32, 98},
        {Symbol::boxed_i32, 99},
        {Symbol::boxed_i32, 100},
};

const BaseTerm<int64_t> Term::i64_memo[201] = {
        {Symbol::boxed_i64, -100},
        {Symbol::boxed_i64, -99},
        {Symbol::boxed_i64, -98},
        {Symbol::boxed_i64, -97},
        {Symbol::boxed_i64, -96},
        {Symbol::boxed_i64, -95},
        {Symbol::boxed_i64, -94},
        {Symbol::boxed_i64, -93},
        {Symbol::boxed_i64, -92},
        {Symbol::boxed_i64, -91},
        {Symbol::boxed_i64, -90},
        {Symbol::boxed_i64, -89},
        {Symbol::boxed_i64, -88},
        {Symbol::boxed_i64, -87},
        {Symbol::boxed_i64, -86},
        {Symbol::boxed_i64, -85},
        {Symbol::boxed_i64, -84},
        {Symbol::boxed_i64, -83},
        {Symbol::boxed_i64, -82},
        {Symbol::boxed_i64, -81},
        {Symbol::boxed_i64, -80},
        {Symbol::boxed_i64, -79},
        {Symbol::boxed_i64, -78},
        {Symbol::boxed_i64, -77},
        {Symbol::boxed_i64, -76},
        {Symbol::boxed_i64, -75},
        {Symbol::boxed_i64, -74},
        {Symbol::boxed_i64, -73},
        {Symbol::boxed_i64, -72},
        {Symbol::boxed_i64, -71},
        {Symbol::boxed_i64, -70},
        {Symbol::boxed_i64, -69},
        {Symbol::boxed_i64, -68},
        {Symbol::boxed_i64, -67},
        {Symbol::boxed_i64, -66},
        {Symbol::boxed_i64, -65},
        {Symbol::boxed_i64, -64},
        {Symbol::boxed_i64, -63},
        {Symbol::boxed_i64, -62},
        {Symbol::boxed_i64, -61},
        {Symbol::boxed_i64, -60},
        {Symbol::boxed_i64, -59},
        {Symbol::boxed_i64, -58},
        {Symbol::boxed_i64, -57},
        {Symbol::boxed_i64, -56},
        {Symbol::boxed_i64, -55},
        {Symbol::boxed_i64, -54},
        {Symbol::boxed_i64, -53},
        {Symbol::boxed_i64, -52},
        {Symbol::boxed_i64, -51},
        {Symbol::boxed_i64, -50},
        {Symbol::boxed_i64, -49},
        {Symbol::boxed_i64, -48},
        {Symbol::boxed_i64, -47},
        {Symbol::boxed_i64, -46},
        {Symbol::boxed_i64, -45},
        {Symbol::boxed_i64, -44},
        {Symbol::boxed_i64, -43},
        {Symbol::boxed_i64, -42},
        {Symbol::boxed_i64, -41},
        {Symbol::boxed_i64, -40},
        {Symbol::boxed_i64, -39},
        {Symbol::boxed_i64, -38},
        {Symbol::boxed_i64, -37},
        {Symbol::boxed_i64, -36},
        {Symbol::boxed_i64, -35},
        {Symbol::boxed_i64, -34},
        {Symbol::boxed_i64, -33},
        {Symbol::boxed_i64, -32},
        {Symbol::boxed_i64, -31},
        {Symbol::boxed_i64, -30},
        {Symbol::boxed_i64, -29},
        {Symbol::boxed_i64, -28},
        {Symbol::boxed_i64, -27},
        {Symbol::boxed_i64, -26},
        {Symbol::boxed_i64, -25},
        {Symbol::boxed_i64, -24},
        {Symbol::boxed_i64, -23},
        {Symbol::boxed_i64, -22},
        {Symbol::boxed_i64, -21},
        {Symbol::boxed_i64, -20},
        {Symbol::boxed_i64, -19},
        {Symbol::boxed_i64, -18},
        {Symbol::boxed_i64, -17},
        {Symbol::boxed_i64, -16},
        {Symbol::boxed_i64, -15},
        {Symbol::boxed_i64, -14},
        {Symbol::boxed_i64, -13},
        {Symbol::boxed_i64, -12},
        {Symbol::boxed_i64, -11},
        {Symbol::boxed_i64, -10},
        {Symbol::boxed_i64, -9},
        {Symbol::boxed_i64, -8},
        {Symbol::boxed_i64, -7},
        {Symbol::boxed_i64, -6},
        {Symbol::boxed_i64, -5},
        {Symbol::boxed_i64, -4},
        {Symbol::boxed_i64, -3},
        {Symbol::boxed_i64, -2},
        {Symbol::boxed_i64, -1},
        {Symbol::boxed_i64, 0},
        {Symbol::boxed_i64, 1},
        {Symbol::boxed_i64, 2},
        {Symbol::boxed_i64, 3},
        {Symbol::boxed_i64, 4},
        {Symbol::boxed_i64, 5},
        {Symbol::boxed_i64, 6},
        {Symbol::boxed_i64, 7},
        {Symbol::boxed_i64, 8},
        {Symbol::boxed_i64, 9},
        {Symbol::boxed_i64, 10},
        {Symbol::boxed_i64, 11},
        {Symbol::boxed_i64, 12},
        {Symbol::boxed_i64, 13},
        {Symbol::boxed_i64, 14},
        {Symbol::boxed_i64, 15},
        {Symbol::boxed_i64, 16},
        {Symbol::boxed_i64, 17},
        {Symbol::boxed_i64, 18},
        {Symbol::boxed_i64, 19},
        {Symbol::boxed_i64, 20},
        {Symbol::boxed_i64, 21},
        {Symbol::boxed_i64, 22},
        {Symbol::boxed_i64, 23},
        {Symbol::boxed_i64, 24},
        {Symbol::boxed_i64, 25},
        {Symbol::boxed_i64, 26},
        {Symbol::boxed_i64, 27},
        {Symbol::boxed_i64, 28},
        {Symbol::boxed_i64, 29},
        {Symbol::boxed_i64, 30},
        {Symbol::boxed_i64, 31},
        {Symbol::boxed_i64, 32},
        {Symbol::boxed_i64, 33},
        {Symbol::boxed_i64, 34},
        {Symbol::boxed_i64, 35},
        {Symbol::boxed_i64, 36},
        {Symbol::boxed_i64, 37},
        {Symbol::boxed_i64, 38},
        {Symbol::boxed_i64, 39},
        {Symbol::boxed_i64, 40},
        {Symbol::boxed_i64, 41},
        {Symbol::boxed_i64, 42},
        {Symbol::boxed_i64, 43},
        {Symbol::boxed_i64, 44},
        {Symbol::boxed_i64, 45},
        {Symbol::boxed_i64, 46},
        {Symbol::boxed_i64, 47},
        {Symbol::boxed_i64, 48},
        {Symbol::boxed_i64, 49},
        {Symbol::boxed_i64, 50},
        {Symbol::boxed_i64, 51},
        {Symbol::boxed_i64, 52},
        {Symbol::boxed_i64, 53},
        {Symbol::boxed_i64, 54},
        {Symbol::boxed_i64, 55},
        {Symbol::boxed_i64, 56},
        {Symbol::boxed_i64, 57},
        {Symbol::boxed_i64, 58},
        {Symbol::boxed_i64, 59},
        {Symbol::boxed_i64, 60},
        {Symbol::boxed_i64, 61},
        {Symbol::boxed_i64, 62},
        {Symbol::boxed_i64, 63},
        {Symbol::boxed_i64, 64},
        {Symbol::boxed_i64, 65},
        {Symbol::boxed_i64, 66},
        {Symbol::boxed_i64, 67},
        {Symbol::boxed_i64, 68},
        {Symbol::boxed_i64, 69},
        {Symbol::boxed_i64, 70},
        {Symbol::boxed_i64, 71},
        {Symbol::boxed_i64, 72},
        {Symbol::boxed_i64, 73},
        {Symbol::boxed_i64, 74},
        {Symbol::boxed_i64, 75},
        {Symbol::boxed_i64, 76},
        {Symbol::boxed_i64, 77},
        {Symbol::boxed_i64, 78},
        {Symbol::boxed_i64, 79},
        {Symbol::boxed_i64, 80},
        {Symbol::boxed_i64, 81},
        {Symbol::boxed_i64, 82},
        {Symbol::boxed_i64, 83},
        {Symbol::boxed_i64, 84},
        {Symbol::boxed_i64, 85},
        {Symbol::boxed_i64, 86},
        {Symbol::boxed_i64, 87},
        {Symbol::boxed_i64, 88},
        {Symbol::boxed_i64, 89},
        {Symbol::boxed_i64, 90},
        {Symbol::boxed_i64, 91},
        {Symbol::boxed_i64, 92},
        {Symbol::boxed_i64, 93},
        {Symbol::boxed_i64, 94},
        {Symbol::boxed_i64, 95},
        {Symbol::boxed_i64, 96},
        {Symbol::boxed_i64, 97},
        {Symbol::boxed_i64, 98},
        {Symbol::boxed_i64, 99},
        {Symbol::boxed_i64, 100},
};

}
