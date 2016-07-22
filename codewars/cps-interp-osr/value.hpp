#ifndef _VALUE_HPP
#define _VALUE_HPP

#include <cstdint>

#include "info.hpp"
#include "common.hpp"

class Value final {
 public:
  Value(Info *info) {
    info_ = info;
  }

  Value *&at(intptr_t ix) {
    DCHECK(ix >= 0 && ix < info_->numPtrs());
    return payloads_[ix];
  }

  intptr_t &wordAt(intptr_t ix) {
    DCHECK(ix >= info_->numPtrs() && ix < info_->numPayloads());
    return *reinterpret_cast<intptr_t **>(payloads_)[ix];
  }

  Info &info() {
    return *info_;
  }

 private:
  Info *info_;
  Value *payloads_[0];
};

#endif  // _VALUE_HPP
