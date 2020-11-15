package com.github.om.soothello.analyzee;

import javax.annotation.Nonnull;

public interface IFactory<A> {
    @Nonnull
    A create();
}
