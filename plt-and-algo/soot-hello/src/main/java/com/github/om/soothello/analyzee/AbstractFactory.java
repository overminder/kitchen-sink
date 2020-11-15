package com.github.om.soothello.analyzee;

import javax.annotation.Nonnull;

public abstract class AbstractFactory<A> implements IFactory<A> {

    final Class<A> klass;
    private DepResolver resolver;

    protected AbstractFactory(@Nonnull Class<A> klass) {
        this.klass = klass;
    }

    final void setResolver(@Nonnull DepResolver resolver) {
        RuntimeChecks.require(this.resolver == null, this + " already attached to resolver");
        this.resolver = resolver;
    }

    final protected <B> B getDep(@Nonnull Class<B> kls) {
        RuntimeChecks.require(resolver != null, this + " not yet attached to resolver");
        return resolver.resolve(kls);
    }
}
