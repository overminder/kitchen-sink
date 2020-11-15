package com.github.om.soothello.analyzee;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;

public interface IService<A> {
    void put(@Nonnull A a, int id);

    @Nullable
    A get(int id);
}
