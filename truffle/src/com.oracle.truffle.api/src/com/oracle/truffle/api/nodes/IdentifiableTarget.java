package com.oracle.truffle.api.nodes;

import java.util.concurrent.atomic.AtomicInteger;

public abstract class IdentifiableTarget {

    public final int id;
    private static final AtomicInteger idCounter = new AtomicInteger(0);

    protected IdentifiableTarget() {
        this.id = idCounter.getAndIncrement();
    }
}
