#ifndef _INFO_HPP
#define _INFO_HPP

#include "common.hpp"

#include <cstdint>
#include <vector>
#include <memory>

class Info final {
 public:
  Info(int16_t numPayloads, int16_t numPtrs, int16_t arity) {
    DCHECK(numPayloads >= 0 && numPayloads >= numPtrs);
    DCHECK(numPtrs >= 0);
    DCHECK(arity >= 0);

    numPayloads_ = numPayloads;
    numPtrs_ = numPtrs;
    arity_ = arity;
    callCount_ = 0;
  }

  int16_t numPtrs() {
    return numPtrs_;
  }

  int16_t numPayloads() {
    return numPayloads_;
  }

  std::vector<uint8_t> &bytecodes() {
    return bytecodes_;
  }

 private:
  int16_t numPayloads_;
  int16_t numPtrs_;
  int16_t arity_;
  int16_t callCount_;
  std::vector<uint8_t> bytecodes_;
};

#endif  // _INFO_HPP
