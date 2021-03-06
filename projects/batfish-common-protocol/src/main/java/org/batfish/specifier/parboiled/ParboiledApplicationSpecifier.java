package org.batfish.specifier.parboiled;

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;
import java.util.Objects;
import java.util.Set;
import javax.annotation.Nonnull;
import javax.annotation.ParametersAreNonnullByDefault;
import org.batfish.datamodel.Protocol;
import org.batfish.specifier.ApplicationSpecifier;

/** An {@link ApplicationSpecifier} that resolves based on the AST generated by {@link Parser}. */
@ParametersAreNonnullByDefault
final class ParboiledApplicationSpecifier implements ApplicationSpecifier {

  @ParametersAreNonnullByDefault
  private final class ApplicationAstNodeToApplications
      implements ApplicationAstNodeVisitor<Set<Protocol>> {

    ApplicationAstNodeToApplications() {}

    @Nonnull
    @Override
    public Set<Protocol> visitNameApplicationAstNode(
        NameApplicationAstNode nameApplicationAstNode) {
      return ImmutableSet.of(nameApplicationAstNode.getProtocol());
    }

    @Nonnull
    @Override
    public Set<Protocol> visitUnionApplicationAstNode(
        UnionApplicationAstNode unionApplicationAstNode) {
      return Sets.union(
          unionApplicationAstNode.getLeft().accept(this),
          unionApplicationAstNode.getRight().accept(this));
    }
  }

  private final ApplicationAstNode _ast;

  ParboiledApplicationSpecifier(ApplicationAstNode ast) {
    _ast = ast;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) {
      return true;
    }
    if (!(o instanceof ParboiledApplicationSpecifier)) {
      return false;
    }
    return Objects.equals(_ast, ((ParboiledApplicationSpecifier) o)._ast);
  }

  @Override
  public int hashCode() {
    return Objects.hash(_ast);
  }

  @Override
  public Set<Protocol> resolve() {
    return _ast.accept(new ApplicationAstNodeToApplications());
  }
}
