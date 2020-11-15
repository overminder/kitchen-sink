package com.github.om.soothello.analyzee;

import javax.annotation.Nonnull;

public class FooResourceFactory extends AbstractFactory<FooResource> {

    FooResourceFactory() {
        super(FooResource.class);
    }

    @Nonnull
    @Override
    public FooResource create() {
        return new FooResource(getDep(FooService.class));
    }
}
