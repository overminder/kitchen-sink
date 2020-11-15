package com.github.om.soothello.analyzee;

import javax.annotation.Nonnull;

public class RuntimeChecks {
    public static void require(boolean x, @Nonnull String message) {
        if (!x) {
            throw new RuntimeException(message);
        }
    }
}
