package com.github.mauricioaniche.ck;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Set;
import java.util.Stack;
import java.util.concurrent.Callable;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.AbstractTypeDeclaration;
import org.eclipse.jdt.core.dom.AnnotationTypeDeclaration;
import org.eclipse.jdt.core.dom.AnnotationTypeMemberDeclaration;
import org.eclipse.jdt.core.dom.AnonymousClassDeclaration;
import org.eclipse.jdt.core.dom.ArrayAccess;
import org.eclipse.jdt.core.dom.ArrayCreation;
import org.eclipse.jdt.core.dom.ArrayInitializer;
import org.eclipse.jdt.core.dom.ArrayType;
import org.eclipse.jdt.core.dom.AssertStatement;
import org.eclipse.jdt.core.dom.Assignment;
import org.eclipse.jdt.core.dom.Block;
import org.eclipse.jdt.core.dom.BlockComment;
import org.eclipse.jdt.core.dom.BodyDeclaration;
import org.eclipse.jdt.core.dom.BooleanLiteral;
import org.eclipse.jdt.core.dom.BreakStatement;
import org.eclipse.jdt.core.dom.CastExpression;
import org.eclipse.jdt.core.dom.CatchClause;
import org.eclipse.jdt.core.dom.CharacterLiteral;
import org.eclipse.jdt.core.dom.ClassInstanceCreation;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.ConditionalExpression;
import org.eclipse.jdt.core.dom.ConstructorInvocation;
import org.eclipse.jdt.core.dom.ContinueStatement;
import org.eclipse.jdt.core.dom.CreationReference;
import org.eclipse.jdt.core.dom.Dimension;
import org.eclipse.jdt.core.dom.DoStatement;
import org.eclipse.jdt.core.dom.EmptyStatement;
import org.eclipse.jdt.core.dom.EnhancedForStatement;
import org.eclipse.jdt.core.dom.EnumConstantDeclaration;
import org.eclipse.jdt.core.dom.EnumDeclaration;
import org.eclipse.jdt.core.dom.ExpressionMethodReference;
import org.eclipse.jdt.core.dom.ExpressionStatement;
import org.eclipse.jdt.core.dom.FieldAccess;
import org.eclipse.jdt.core.dom.FieldDeclaration;
import org.eclipse.jdt.core.dom.ForStatement;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IfStatement;
import org.eclipse.jdt.core.dom.ImportDeclaration;
import org.eclipse.jdt.core.dom.InfixExpression;
import org.eclipse.jdt.core.dom.Initializer;
import org.eclipse.jdt.core.dom.InstanceofExpression;
import org.eclipse.jdt.core.dom.IntersectionType;
import org.eclipse.jdt.core.dom.Javadoc;
import org.eclipse.jdt.core.dom.LabeledStatement;
import org.eclipse.jdt.core.dom.LambdaExpression;
import org.eclipse.jdt.core.dom.LineComment;
import org.eclipse.jdt.core.dom.MarkerAnnotation;
import org.eclipse.jdt.core.dom.MemberRef;
import org.eclipse.jdt.core.dom.MemberValuePair;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.MethodInvocation;
import org.eclipse.jdt.core.dom.MethodRef;
import org.eclipse.jdt.core.dom.MethodRefParameter;
import org.eclipse.jdt.core.dom.Modifier;
import org.eclipse.jdt.core.dom.NameQualifiedType;
import org.eclipse.jdt.core.dom.NormalAnnotation;
import org.eclipse.jdt.core.dom.NullLiteral;
import org.eclipse.jdt.core.dom.NumberLiteral;
import org.eclipse.jdt.core.dom.PackageDeclaration;
import org.eclipse.jdt.core.dom.ParameterizedType;
import org.eclipse.jdt.core.dom.ParenthesizedExpression;
import org.eclipse.jdt.core.dom.PostfixExpression;
import org.eclipse.jdt.core.dom.PrefixExpression;
import org.eclipse.jdt.core.dom.PrimitiveType;
import org.eclipse.jdt.core.dom.QualifiedName;
import org.eclipse.jdt.core.dom.QualifiedType;
import org.eclipse.jdt.core.dom.ReturnStatement;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.core.dom.SimpleType;
import org.eclipse.jdt.core.dom.SingleMemberAnnotation;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;
import org.eclipse.jdt.core.dom.StringLiteral;
import org.eclipse.jdt.core.dom.SuperConstructorInvocation;
import org.eclipse.jdt.core.dom.SuperFieldAccess;
import org.eclipse.jdt.core.dom.SuperMethodInvocation;
import org.eclipse.jdt.core.dom.SuperMethodReference;
import org.eclipse.jdt.core.dom.SwitchCase;
import org.eclipse.jdt.core.dom.SwitchStatement;
import org.eclipse.jdt.core.dom.SynchronizedStatement;
import org.eclipse.jdt.core.dom.TagElement;
import org.eclipse.jdt.core.dom.TextElement;
import org.eclipse.jdt.core.dom.ThisExpression;
import org.eclipse.jdt.core.dom.ThrowStatement;
import org.eclipse.jdt.core.dom.TryStatement;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.core.dom.TypeDeclarationStatement;
import org.eclipse.jdt.core.dom.TypeLiteral;
import org.eclipse.jdt.core.dom.TypeMethodReference;
import org.eclipse.jdt.core.dom.TypeParameter;
import org.eclipse.jdt.core.dom.UnionType;
import org.eclipse.jdt.core.dom.VariableDeclarationExpression;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;
import org.eclipse.jdt.core.dom.VariableDeclarationStatement;
import org.eclipse.jdt.core.dom.WhileStatement;
import org.eclipse.jdt.core.dom.WildcardType;

import com.github.mauricioaniche.ck.metric.CKASTVisitor;
import com.github.mauricioaniche.ck.metric.ClassLevelMetric;
import com.github.mauricioaniche.ck.metric.MethodLevelMetric;
import com.github.mauricioaniche.ck.util.JDTUtils;
import static com.github.mauricioaniche.ck.util.LOCCalculator.calculate;

public class CKVisitor extends ASTVisitor {

	private String sourceFilePath;
	private int anonymousNumber;
	private int initializerNumber;

	class MethodInTheStack {
		CKMethodResult result;
		List<MethodLevelMetric> methodLevelMetrics;
	}

	class ClassInTheStack {
		CKClassResult result;
		List<ClassLevelMetric> classLevelMetrics;
		Stack<MethodInTheStack> methods;


		ClassInTheStack() {
			methods = new Stack<>();
		}
	}

	private Stack<ClassInTheStack> classes;

	private Set<CKClassResult> collectedClasses;

	private CompilationUnit cu;
	private Callable<List<ClassLevelMetric>> classLevelMetrics;
	private Callable<List<MethodLevelMetric>> methodLevelMetrics;

	public CKVisitor(String sourceFilePath, CompilationUnit cu,
			Callable<List<ClassLevelMetric>> classLevelMetrics,
			Callable<List<MethodLevelMetric>> methodLevelMetrics) {
		this.sourceFilePath = sourceFilePath;
		this.cu = cu;
		this.classLevelMetrics = classLevelMetrics;
		this.methodLevelMetrics = methodLevelMetrics;
		this.classes = new Stack<>();
		this.collectedClasses = new HashSet<>();
	}

	@Override
	public boolean visit(TypeDeclaration node) {
		ITypeBinding binding = node.resolveBinding();

		// build a CKClassResult based on the current type
		// declaration we are visiting
		String className=node.getName().getFullyQualifiedName();// binding != null ? binding.getBinaryName()
		// : cu.getPackage().getName().getFullyQualifiedName();
		ASTNode parentNode = node.getParent();
		boolean hasAnonymousClass = false;
		while (parentNode != null) {
			if (parentNode instanceof AnonymousClassDeclaration) {
				hasAnonymousClass = true;
				break;
			}
			parentNode = parentNode.getParent();
		}
		if (binding != null && !hasAnonymousClass) {
			className = binding.getBinaryName()+"000";
		} else {
			List<String> classList = new ArrayList<>();
			String packageName = cu.getPackage().getName().getFullyQualifiedName();
			ASTNode tmpNode = node;
			while (tmpNode != null) {
				if (tmpNode instanceof AnonymousClassDeclaration) {
					AnonymousClassDeclaration anonymousNode = (AnonymousClassDeclaration) tmpNode;
					int anonymousNodePosition = anonymousNode.getStartPosition();
					Integer anonymousStartLine = cu.getLineNumber(anonymousNodePosition);
					classList.add(anonymousStartLine.toString());
				} else if (tmpNode instanceof BodyDeclaration) {
					BodyDeclaration bodyNode = (BodyDeclaration) tmpNode;
					if (bodyNode instanceof AbstractTypeDeclaration) {
						AbstractTypeDeclaration abstractNode = (AbstractTypeDeclaration) bodyNode;
						classList.add(abstractNode.getName().getFullyQualifiedName());
					}
				}
				tmpNode = tmpNode.getParent();
			}
			className = packageName;
			ListIterator<String> it = classList.listIterator(classList.size());
			boolean isFirstFactor = true;
			while (it.hasPrevious()) {
				if (isFirstFactor) {
					className = className + "." + it.previous();
					isFirstFactor = false;
				} else {
					className = className + "$" + it.previous();
				}
			}
		}
		String type = getTypeOfTheUnit(node);
		int modifiers = node.getModifiers();
		CKClassResult currentClass = new CKClassResult(sourceFilePath, className, type, modifiers);
		currentClass.setLoc(calculate(node.toString()));

		// there might be metrics that use it
		// (even before a class is declared)
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));

		}

		// create a set of visitors, just for the current class
		List<ClassLevelMetric> classLevelMetrics = instantiateClassLevelMetricVisitors(className);

		// store everything in a 'class in the stack' data structure
		ClassInTheStack classInTheStack = new ClassInTheStack();
		classInTheStack.result = currentClass;
		classInTheStack.classLevelMetrics = classLevelMetrics;

		// push it to the stack, so we know the current class we are visiting
		classes.push(classInTheStack);

		// there might be class level metrics that use the TypeDeclaration
		// so, let's run them
		classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
				.forEach(ast -> ast.visit(node));

		return true;
	}


	@Override
	public void endVisit(TypeDeclaration node) {

		// let's first visit any metrics that might make use of this endVisit
		classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
				.forEach(ast -> ast.endVisit(node));

		ClassInTheStack completedClass = classes.pop();

		// persist the results of the class level metrics in the result
		completedClass.classLevelMetrics.forEach(m -> m.setResult(completedClass.result));

		// we are done processing this class, so now let's
		// store it in the collected classes set
		collectedClasses.add(completedClass.result);
	}

	public boolean visit(MethodDeclaration node) {

		IMethodBinding binding = node.resolveBinding();
		String currentMethodName = JDTUtils.getMethodFullName(node);
		String currentQualifiedMethodName = JDTUtils.getQualifiedMethodFullName(node);
		boolean isConstructor = node.isConstructor();

		String className =
				((currentQualifiedMethodName.lastIndexOf(currentMethodName) - 1) > 0)
						? currentQualifiedMethodName.substring(0,
								(currentQualifiedMethodName.lastIndexOf(currentMethodName) - 1))
						: "";

		CKMethodResult currentMethod = new CKMethodResult(currentMethodName,
				currentQualifiedMethodName, isConstructor, node.getModifiers());
		currentMethod.setLoc(calculate(node.toString()));

		int methodPosition = node.getName().getStartPosition();
		int methodStartLine = cu.getLineNumber(methodPosition);
		currentMethod.setStartLine(methodStartLine);

		// let's instantiate method level visitors for this current method
		List<MethodLevelMetric> methodLevelMetrics =
				instantiateMethodLevelMetricVisitors(currentQualifiedMethodName);

		// we add it to the current class we are visiting
		MethodInTheStack methodInTheStack = new MethodInTheStack();
		methodInTheStack.result = currentMethod;
		methodInTheStack.methodLevelMetrics = methodLevelMetrics;
		classes.peek().methods.push(methodInTheStack);

		// and there might be metrics that also use the methoddeclaration node.
		// so, let's call them
		classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
				.forEach(ast -> ast.visit(node));
		if (!classes.peek().methods.isEmpty())
			classes.peek().methods.peek().methodLevelMetrics.stream()
					.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));

		return true;
	}

	@Override
	public void endVisit(MethodDeclaration node) {

		// let's first invoke the metrics, because they might use this node
		classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
				.forEach(ast -> ast.endVisit(node));
		classes.peek().methods.peek().methodLevelMetrics.stream()
				.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.endVisit(node));

		// remove the method from the stack
		MethodInTheStack completedMethod = classes.peek().methods.pop();

		// persist the data of the visitors in the CKMethodResult
		completedMethod.methodLevelMetrics.forEach(m -> m.setResult(completedMethod.result));

		// store its final version in the current class
		classes.peek().result.addMethod(completedMethod.result);
	}


	public boolean visit(AnonymousClassDeclaration node) {
		java.util.List<String> stringList = new java.util.ArrayList<>();
		stringList = stringList.stream().map(string -> string.toString())
				.collect(java.util.stream.Collectors.toList());

		// there might be metrics that use it
		// (even before an anonymous class is created)
		classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
				.forEach(ast -> ast.visit(node));
		if (!classes.peek().methods.isEmpty())
			classes.peek().methods.peek().methodLevelMetrics.stream()
					.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));

		// we give the anonymous class a 'class$AnonymousN' name
		int anonymousposition = node.getStartPosition();
		int anonymousline = cu.getLineNumber(anonymousposition);

		String anonClassName = classes.peek().result.getClassName() + "$Anonymous" + anonymousline;
		CKClassResult currentClass =
				new CKClassResult(sourceFilePath, anonClassName, "anonymous", -1);
		currentClass.setLoc(calculate(node.toString()));

		// create a set of visitors, just for the current class
		List<ClassLevelMetric> classLevelMetrics =
				instantiateClassLevelMetricVisitors(anonClassName);

		// store everything in a 'class in the stack' data structure
		ClassInTheStack classInTheStack = new ClassInTheStack();
		classInTheStack.result = currentClass;
		classInTheStack.classLevelMetrics = classLevelMetrics;

		// push it to the stack, so we know the current class we are visiting
		classes.push(classInTheStack);

		// and there might be metrics that also use the methoddeclaration node.
		// so, let's call them
		classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
				.forEach(ast -> ast.visit(node));
		if (!classes.peek().methods.isEmpty())
			classes.peek().methods.peek().methodLevelMetrics.stream()
					.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));

		return true;
	}

	public void endVisit(AnonymousClassDeclaration node) {

		classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
				.forEach(ast -> ast.endVisit(node));

		ClassInTheStack completedClass = classes.pop();

		// persist the results of the class level metrics in the result
		completedClass.classLevelMetrics.forEach(m -> m.setResult(completedClass.result));

		// we are done processing this class, so now let's
		// store it in the collected classes set
		collectedClasses.add(completedClass.result);
	}

	// static blocks
	public boolean visit(Initializer node) {
		int initializerposition = node.getStartPosition();
		int initailizerline = cu.getLineNumber(initializerposition);
		String currentMethodName = "(initializer " + initailizerline + ")";

		CKMethodResult currentMethod = new CKMethodResult(currentMethodName, currentMethodName,
				false, node.getModifiers());
		currentMethod.setLoc(calculate(node.toString()));
		currentMethod.setStartLine(JDTUtils.getStartLine(cu, node));

		// let's instantiate method level visitors for this current method
		List<MethodLevelMetric> methodLevelMetrics =
				instantiateMethodLevelMetricVisitors(currentMethodName);

		// we add it to the current class we are visiting
		MethodInTheStack methodInTheStack = new MethodInTheStack();
		methodInTheStack.result = currentMethod;
		methodInTheStack.methodLevelMetrics = methodLevelMetrics;
		classes.peek().methods.push(methodInTheStack);

		// and there might be metrics that also use the methoddeclaration node.
		// so, let's call them
		classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
				.forEach(ast -> ast.visit(node));
		if (!classes.peek().methods.isEmpty())
			classes.peek().methods.peek().methodLevelMetrics.stream()
					.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));

		return true;
	}

	@Override
	public void endVisit(Initializer node) {

		// let's first invoke the metrics, because they might use this node
		classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
				.forEach(ast -> ast.endVisit(node));
		classes.peek().methods.peek().methodLevelMetrics.stream()
				.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.endVisit(node));

		// remove the method from the stack
		MethodInTheStack completedMethod = classes.peek().methods.pop();

		// persist the data of the visitors in the CKMethodResult
		completedMethod.methodLevelMetrics.forEach(m -> m.setResult(completedMethod.result));

		// store its final version in the current class
		classes.peek().result.addMethod(completedMethod.result);
	}


	public boolean visit(EnumDeclaration node) {
		ITypeBinding binding = node.resolveBinding();

		// there might be metrics that use it
		// (even before a enum is declared)
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}

		// build a CKClassResult based on the current type
		// declaration we are visiting
		ASTNode parentNode = node.getParent();
		boolean hasAnonymousClass = false;
		while (parentNode != null) {
			if (parentNode instanceof AnonymousClassDeclaration) {
				hasAnonymousClass = true;
				break;
			}
			parentNode = parentNode.getParent();
		}
		String className=node.getName().getFullyQualifiedName();
		if (binding != null && !hasAnonymousClass) {
			className = binding.getBinaryName()+"000";
		} else {
			List<String> classList = new ArrayList<>();
			String packageName = cu.getPackage().getName().getFullyQualifiedName();
			ASTNode tmpNode = node;
			while (tmpNode != null) {
				if (tmpNode instanceof AnonymousClassDeclaration) {
					AnonymousClassDeclaration anonymousNode = (AnonymousClassDeclaration) tmpNode;
					int anonymousNodePosition = anonymousNode.getStartPosition();
					Integer anonymousStartLine = cu.getLineNumber(anonymousNodePosition);
					classList.add(anonymousStartLine.toString());
				} else if (tmpNode instanceof BodyDeclaration) {
					BodyDeclaration bodyNode = (BodyDeclaration) tmpNode;
					if (bodyNode instanceof AbstractTypeDeclaration) {
						AbstractTypeDeclaration abstractNode = (AbstractTypeDeclaration) bodyNode;
						classList.add(abstractNode.getName().getFullyQualifiedName());
					}
				}
				tmpNode = tmpNode.getParent();
				className = packageName;
				ListIterator<String> it = classList.listIterator(classList.size());
				boolean isFirstFactor = true;
				while (it.hasPrevious()) {
					if (isFirstFactor) {
						className = className + "." + it.previous();
						isFirstFactor = false;
					} else {
						className = className + "$" + it.previous();
					}
				}
			}

		}
		String type = "enum";
		int modifiers = node.getModifiers();
		CKClassResult currentClass = new CKClassResult(sourceFilePath, className, type, modifiers);
		currentClass.setLoc(calculate(node.toString()));

		// create a set of visitors, just for the current class
		List<ClassLevelMetric> classLevelMetrics = instantiateClassLevelMetricVisitors(className);

		// store everything in a 'class in the stack' data structure
		ClassInTheStack classInTheStack = new ClassInTheStack();
		classInTheStack.result = currentClass;
		classInTheStack.classLevelMetrics = classLevelMetrics;

		// push it to the stack, so we know the current class we are visiting
		classes.push(classInTheStack);

		// there might be class level metrics that use the TypeDeclaration
		// so, let's run them
		classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
				.forEach(ast -> ast.visit(node));

		return true;

	}

	@Override
	public void endVisit(EnumDeclaration node) {
		// let's first visit any metrics that might make use of this endVisit
		classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
				.forEach(ast -> ast.endVisit(node));

		ClassInTheStack completedClass = classes.pop();

		// persist the results of the class level metrics in the result
		completedClass.classLevelMetrics.forEach(m -> m.setResult(completedClass.result));

		// we are done processing this class, so now let's
		// store it in the collected classes set
		collectedClasses.add(completedClass.result);
	}

	private List<ClassLevelMetric> instantiateClassLevelMetricVisitors(String className) {
		try {
			List<ClassLevelMetric> classes = classLevelMetrics.call();
			classes.forEach(c -> {
				c.setClassName(className);
			});
			return classes;
			// return classLevelMetrics.call();
		} catch (Exception e) {
			throw new RuntimeException("Could not instantiate class level visitors", e);
		}
	}

	private List<MethodLevelMetric> instantiateMethodLevelMetricVisitors(String methodName) {
		try {
			List<MethodLevelMetric> methods = methodLevelMetrics.call();
			methods.forEach(m -> {
				m.setMethodName(methodName);
			});
			return methods;
			// return methodLevelMetrics.call();
		} catch (Exception e) {
			throw new RuntimeException("Could not instantiate method level visitors", e);
		}
	}

	public Set<CKClassResult> getCollectedClasses() {
		return collectedClasses;
	}

	private String getTypeOfTheUnit(TypeDeclaration node) {
		return node.isInterface() ? "interface" : (classes.isEmpty() ? "class" : "innerclass");
	}

	// -------------------------------------------------------
	// From here, just delegating the calls to the metrics
	public boolean visit(AnnotationTypeDeclaration node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(AnnotationTypeMemberDeclaration node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(ArrayAccess node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(ArrayCreation node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(ArrayInitializer node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(ArrayType node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(AssertStatement node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(Assignment node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(Block node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(BlockComment node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(BooleanLiteral node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(BreakStatement node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(CastExpression node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(CatchClause node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(CharacterLiteral node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(ClassInstanceCreation node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(CompilationUnit node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;
	}

	public boolean visit(ConditionalExpression node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(ConstructorInvocation node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(ContinueStatement node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(CreationReference node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(Dimension node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(DoStatement node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(EmptyStatement node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(EnhancedForStatement node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(EnumConstantDeclaration node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(ExpressionMethodReference node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(ExpressionStatement node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(FieldAccess node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(FieldDeclaration node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(ForStatement node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(IfStatement node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(ImportDeclaration node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(InfixExpression node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(InstanceofExpression node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(IntersectionType node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(LabeledStatement node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(LambdaExpression node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(LineComment node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(MarkerAnnotation node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(MemberRef node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(MemberValuePair node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(MethodRef node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(MethodRefParameter node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(MethodInvocation node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(Modifier node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(NameQualifiedType node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(NormalAnnotation node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(NullLiteral node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(NumberLiteral node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(PackageDeclaration node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(ParameterizedType node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(ParenthesizedExpression node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(PostfixExpression node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(PrefixExpression node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(PrimitiveType node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(QualifiedName node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(QualifiedType node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(ReturnStatement node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(SimpleName node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(SimpleType node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(SingleMemberAnnotation node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(SingleVariableDeclaration node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(StringLiteral node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(SuperConstructorInvocation node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(SuperFieldAccess node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(SuperMethodInvocation node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(SuperMethodReference node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(SwitchCase node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(SwitchStatement node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(SynchronizedStatement node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(TagElement node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(TextElement node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(ThisExpression node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(ThrowStatement node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(TryStatement node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(TypeDeclarationStatement node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(TypeLiteral node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(TypeMethodReference node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(TypeParameter node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(UnionType node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(VariableDeclarationExpression node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(VariableDeclarationStatement node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(VariableDeclarationFragment node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(WhileStatement node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	public boolean visit(WildcardType node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	// we only visit if we found a type already.
	// TODO: understand what happens with a javadoc in a class. Will the TypeDeclaration come first?
	public boolean visit(Javadoc node) {
		if (!classes.isEmpty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.visit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.visit(node));
		}
		return true;

	}

	// ---------------------------------------------
	// End visits

	@Override
	public void endVisit(Block node) {
		classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
				.forEach(ast -> ast.endVisit(node));
		if (!classes.peek().methods.isEmpty())
			classes.peek().methods.peek().methodLevelMetrics.stream()
					.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.endVisit(node));
	}

	@Override
	public void endVisit(FieldAccess node) {
		classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
				.forEach(ast -> ast.endVisit(node));
		if (!classes.peek().methods.isEmpty())
			classes.peek().methods.peek().methodLevelMetrics.stream()
					.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.endVisit(node));
	}

	@Override
	public void endVisit(ConditionalExpression node) {
		classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
				.forEach(ast -> ast.endVisit(node));
		if (!classes.peek().methods.isEmpty())
			classes.peek().methods.peek().methodLevelMetrics.stream()
					.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.endVisit(node));
	}

	public void endVisit(ForStatement node) {
		classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
				.forEach(ast -> ast.endVisit(node));
		if (!classes.peek().methods.isEmpty())
			classes.peek().methods.peek().methodLevelMetrics.stream()
					.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.endVisit(node));
	}

	public void endVisit(EnhancedForStatement node) {
		classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
				.forEach(ast -> ast.endVisit(node));
		if (!classes.peek().methods.isEmpty())
			classes.peek().methods.peek().methodLevelMetrics.stream()
					.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.endVisit(node));
	}

	public void endVisit(DoStatement node) {
		classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
				.forEach(ast -> ast.endVisit(node));
		if (!classes.peek().methods.isEmpty())
			classes.peek().methods.peek().methodLevelMetrics.stream()
					.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.endVisit(node));
	}

	public void endVisit(WhileStatement node) {
		classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
				.forEach(ast -> ast.endVisit(node));
		if (!classes.peek().methods.isEmpty())
			classes.peek().methods.peek().methodLevelMetrics.stream()
					.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.endVisit(node));
	}

	public void endVisit(SwitchCase node) {
		classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
				.forEach(ast -> ast.endVisit(node));
		if (!classes.peek().methods.isEmpty())
			classes.peek().methods.peek().methodLevelMetrics.stream()
					.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.endVisit(node));
	}

	public void endVisit(IfStatement node) {
		classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
				.forEach(ast -> ast.endVisit(node));
		if (!classes.peek().methods.isEmpty())
			classes.peek().methods.peek().methodLevelMetrics.stream()
					.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.endVisit(node));
	}

	public void endVisit(SwitchStatement node) {
		classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
				.forEach(ast -> ast.endVisit(node));
		if (!classes.peek().methods.isEmpty())
			classes.peek().methods.peek().methodLevelMetrics.stream()
					.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.endVisit(node));
	}

	public void endVisit(CatchClause node) {
		classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
				.forEach(ast -> ast.endVisit(node));
		if (!classes.peek().methods.isEmpty())
			classes.peek().methods.peek().methodLevelMetrics.stream()
					.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.endVisit(node));
	}

	public void endVisit(Javadoc node) {
		if (!classes.empty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.endVisit(node));
			if (!classes.peek().methods.isEmpty())
				classes.peek().methods.peek().methodLevelMetrics.stream()
						.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.endVisit(node));
		}
	}

	public void endVisit(QualifiedName node) {
		if (!classes.empty()) {
			classes.peek().classLevelMetrics.stream().map(metric -> (CKASTVisitor) metric)
					.forEach(ast -> ast.endVisit(node));
		}
		if (!classes.isEmpty() && !classes.peek().methods.isEmpty())
			classes.peek().methods.peek().methodLevelMetrics.stream()
					.map(metric -> (CKASTVisitor) metric).forEach(ast -> ast.endVisit(node));
	}
	// TODO: add all other endVisit blocks
}
