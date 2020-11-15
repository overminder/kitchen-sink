package com.github.om.soothello.analyzee;

import javax.annotation.Nonnull;

public class FooServiceFactory extends AbstractFactory<FooService> {

    protected FooServiceFactory() {
        super(FooService.class);
    }

    @Nonnull
    @Override
    public FooService create() {
        return new FooService();
    }
}
