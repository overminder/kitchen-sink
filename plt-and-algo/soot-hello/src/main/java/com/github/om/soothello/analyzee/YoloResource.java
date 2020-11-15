package com.github.om.soothello.analyzee;

import java.lang.annotation.ElementType;
import java.lang.annotation.Target;

@Target(ElementType.TYPE)
public @interface YoloResource {
    String path = "";
}
