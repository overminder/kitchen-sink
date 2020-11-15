package com.github.om.soothello.analyzee;

import java.util.LinkedHashMap;
import java.util.Map;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;

public class FooService implements IService<Foo> {
    private final Map<Integer, Foo> storage = new LinkedHashMap<>();

    @Override
    public void put(@Nonnull Foo foo, int id) {
        storage.put(id, foo);
    }

    @Nullable
    @Override
    public Foo get(int id) {
        return storage.get(id);
    }
}
