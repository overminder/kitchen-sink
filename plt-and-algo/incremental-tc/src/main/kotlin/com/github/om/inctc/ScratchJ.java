package com.github.om.inctc;

import java.lang.annotation.ElementType;
import java.lang.annotation.Target;

public class ScratchJ {
  @Target(ElementType.TYPE_PARAMETER)
  static @interface Foo {
  }

  static class Bar<@Foo A> {
    void foo() {
    }
  }
}
