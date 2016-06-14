/*
 * Copyright (c) 2016, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */
package com.oracle.truffle.dsl.processor.interop;

import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.TypeElement;
import javax.lang.model.type.MirroredTypeException;
import javax.lang.model.type.TypeKind;
import javax.lang.model.type.TypeMirror;

import com.oracle.truffle.api.interop.Message;
import com.oracle.truffle.api.interop.MessageResolution;
import com.oracle.truffle.dsl.processor.java.ElementUtils;

final class Utils {

    static String getTruffleLanguageFullClassName(MessageResolution message) {
        String truffleLanguageFullClazzName;
        try {
            truffleLanguageFullClazzName = message.language().getName();
            throw new AssertionError();
        } catch (MirroredTypeException mte) {
            // This exception is always thrown: use the mirrors to inspect the class
            truffleLanguageFullClazzName = ElementUtils.getQualifiedName(mte.getTypeMirror());
        }
        return truffleLanguageFullClazzName;
    }

    static String getReceiverTypeFullClassName(MessageResolution message) {
        String receiverTypeFullClassName;
        try {
            message.receiverType().getName();
            throw new AssertionError();
        } catch (MirroredTypeException mte) {
            // This exception is always thrown: use the mirrors to inspect the class
            receiverTypeFullClassName = ElementUtils.getQualifiedName(mte.getTypeMirror());
        }
        return receiverTypeFullClassName;
    }

    static Object getMessage(ProcessingEnvironment processingEnv, String messageName) {
        Object currentMessage = null;
        try {
            currentMessage = Message.valueOf(messageName);
        } catch (IllegalArgumentException ex) {
            TypeElement typeElement = processingEnv.getElementUtils().getTypeElement(messageName);
            TypeElement messageElement = processingEnv.getElementUtils().getTypeElement(Message.class.getName());
            if (typeElement != null && processingEnv.getTypeUtils().isAssignable(typeElement.asType(), messageElement.asType())) {
                currentMessage = messageName;
            }
        }
        return currentMessage;
    }

    static TypeMirror getTypeMirror(ProcessingEnvironment env, Class<?> clazz) {
        String name = clazz.getName();
        TypeElement elem = env.getElementUtils().getTypeElement(name);
        return elem.asType();
    }

    static boolean isObjectArray(TypeMirror actualType) {
        return actualType.getKind() == TypeKind.ARRAY && ElementUtils.getQualifiedName(actualType).equals("java.lang.Object");
    }

    static String getFullResolveClassName(TypeElement innerClass) {
        return ElementUtils.getPackageName(innerClass) + "." + getSimpleResolveClassName(innerClass);
    }

    static String getSimpleResolveClassName(TypeElement innerClass) {
        return ElementUtils.getSimpleName(innerClass) + "Sub";
    }

}
