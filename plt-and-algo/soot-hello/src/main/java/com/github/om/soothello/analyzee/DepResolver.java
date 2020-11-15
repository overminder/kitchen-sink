package com.github.om.soothello.analyzee;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import javax.annotation.Nonnull;

public class DepResolver {
    private final Map<Class<?>, Object> resolved = new LinkedHashMap<>();
    private final Map<Class<?>, AbstractFactory<?>> factories = new LinkedHashMap<>();
    private final Set<Class<?>> beingResolved = new LinkedHashSet<>();

    @Nonnull
    <A> A resolve(@Nonnull Class<A> kls) {
        A a = (A) resolved.get(kls);
        if (a != null) {
            return a;
        }

        RuntimeChecks.require(beingResolved.add(kls), "Recursive resolve for " + kls);
        try {
            AbstractFactory<A> af = (AbstractFactory<A>) factories.get(kls);
            RuntimeChecks.require(af != null, "No factory for " + kls);
            a = af.create();
            resolved.put(kls, a);
            return a;
        } finally {
            RuntimeChecks.require(beingResolved.remove(kls), "Someone else removed " + kls);
        }
    }

    public <A> void addFactory(@Nonnull AbstractFactory<A> f) {
        RuntimeChecks.require(factories.put(f.klass, f) == null, "Already has factory for " + f.klass);
        f.setResolver(this);
    }
}
