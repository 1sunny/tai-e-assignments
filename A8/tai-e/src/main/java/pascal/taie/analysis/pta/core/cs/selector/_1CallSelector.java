/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.core.cs.selector;

import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.context.ListContext;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.language.classes.JMethod;

/**
 * Implementation of 1-call-site sensitivity.
 */
public class _1CallSelector implements ContextSelector {

    @Override
    public Context getEmptyContext() {
        return ListContext.make();
    }

// 在调用点敏感中，对静态方法选取上下文的规则和实例方法的相同，
// 即，对于一个静态方法调用，我们组合调用者方法的上下文与调用点本身，
// 来构成被调用方法（本次静态方法调用的目标方法）的上下文。
    @Override
    public Context selectContext(CSCallSite callSite, JMethod callee) {
        // TODO - finish me
        return selectContext(callSite, null, callee);
    }

    @Override
    public Context selectContext(CSCallSite callSite, CSObj recv, JMethod callee) {
        // TODO - finish me
        return ListContext.make(callSite.getCallSite());
    }
// 对每个 k层的 context selector，其堆上下文（heap context）的层数为 k-1 ，
// 举例来说，对一层调用点敏感（1-call-site sensitivity），堆上下文的层数为 0（即没有堆上下文）；
// 对两层调用点敏感（2-call-site sensitivity），堆上下文的层数为 1。
    @Override
    public Context selectHeapContext(CSMethod method, Obj obj) {
        // TODO - finish me
        return getEmptyContext();
    }
}
