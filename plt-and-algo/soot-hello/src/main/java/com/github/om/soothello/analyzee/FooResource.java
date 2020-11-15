package com.github.om.soothello.analyzee;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;

@YoloResource
public class FooResource {
    @Nonnull
    private final IService<Foo> fooService;

    public FooResource(@Nonnull IService<Foo> fooService) {
        this.fooService = fooService;
    }

    @YoloEndpoint
    @Nullable
    public Foo getFoo(int id) {
        return fooService.get(id);
    }
}
