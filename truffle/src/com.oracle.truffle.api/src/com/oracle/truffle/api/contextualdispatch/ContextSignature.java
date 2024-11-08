package com.oracle.truffle.api.contextualdispatch;

public class ContextSignature {
    public long signature;
    public long rootContextSignature;

    public ContextSignature(long signature) {
        this.signature = signature;
        this.rootContextSignature = signature; // a call target won't be necessarily part of a shared subtree
    }

    public void setRootContextSignature(long signature) {
        this.rootContextSignature = signature;
    }

    public void setSelfContextSignature(long signature) {
        this.signature = signature;
    }

    public long getContextSignature() {
        return this.signature;
    }

    public long getRootContextSignature() {
        return this.rootContextSignature;
    }

    public enum ContextualDispatchState {
        NONE,
        DISPATCH_LOCATION,
        SHARED
    }
}

