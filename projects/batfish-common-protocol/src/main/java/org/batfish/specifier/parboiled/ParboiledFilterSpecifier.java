package org.batfish.specifier.parboiled;

import com.google.common.collect.Sets;
import java.util.Objects;
import java.util.Set;
import javax.annotation.Nonnull;
import javax.annotation.ParametersAreNonnullByDefault;
import org.batfish.datamodel.IpAccessList;
import org.batfish.specifier.FilterSpecifier;
import org.batfish.specifier.InterfaceSpecifierFilterSpecifier;
import org.batfish.specifier.NameFilterSpecifier;
import org.batfish.specifier.NameRegexFilterSpecifier;
import org.batfish.specifier.SpecifierContext;

/** An {@link FilterSpecifier} that resolves based on the AST generated by {@link Parser}. */
@ParametersAreNonnullByDefault
final class ParboiledFilterSpecifier implements FilterSpecifier {

  @ParametersAreNonnullByDefault
  private final class FilterAstNodeToFilters implements FilterAstNodeVisitor<Set<IpAccessList>> {
    private final SpecifierContext _ctxt;
    private final String _node;

    FilterAstNodeToFilters(String node, SpecifierContext ctxt) {
      _node = node;
      _ctxt = ctxt;
    }

    @Nonnull
    @Override
    public Set<IpAccessList> visitDifferenceFilterAstNode(
        DifferenceFilterAstNode differenceFilterAstNode) {
      return Sets.difference(
          differenceFilterAstNode.getLeft().accept(this),
          differenceFilterAstNode.getRight().accept(this));
    }

    @Nonnull
    @Override
    public Set<IpAccessList> visitInFilterAstNode(InFilterAstNode inFilterAstNode) {
      return new InterfaceSpecifierFilterSpecifier(
              InterfaceSpecifierFilterSpecifier.Type.IN_FILTER,
              new ParboiledInterfaceSpecifier(inFilterAstNode.getInterfaceAst()))
          .resolve(_node, _ctxt);
    }

    @Nonnull
    @Override
    public Set<IpAccessList> visitIntersectionFilterAstNode(
        IntersectionFilterAstNode intersectionFilterAstNode) {
      return Sets.intersection(
          intersectionFilterAstNode.getLeft().accept(this),
          intersectionFilterAstNode.getRight().accept(this));
    }

    @Nonnull
    @Override
    public Set<IpAccessList> visitNameFilterAstNode(NameFilterAstNode nameFilterAstNode) {
      return new NameFilterSpecifier(nameFilterAstNode.getName()).resolve(_node, _ctxt);
    }

    @Nonnull
    @Override
    public Set<IpAccessList> visitNameRegexFilterAstNode(
        NameRegexFilterAstNode nameRegexFilterAstNode) {
      return new NameRegexFilterSpecifier(nameRegexFilterAstNode.getPattern())
          .resolve(_node, _ctxt);
    }

    @Nonnull
    @Override
    public Set<IpAccessList> visitOutFilterAstNode(OutFilterAstNode inFilterAstNode) {
      return new InterfaceSpecifierFilterSpecifier(
              InterfaceSpecifierFilterSpecifier.Type.OUT_FILTER,
              new ParboiledInterfaceSpecifier(inFilterAstNode.getInterfaceAst()))
          .resolve(_node, _ctxt);
    }

    @Nonnull
    @Override
    public Set<IpAccessList> visitUnionFilterAstNode(UnionFilterAstNode unionFilterAstNode) {
      return Sets.union(
          unionFilterAstNode.getLeft().accept(this), unionFilterAstNode.getRight().accept(this));
    }
  }

  private final FilterAstNode _ast;

  ParboiledFilterSpecifier(FilterAstNode ast) {
    _ast = ast;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) {
      return true;
    }
    if (!(o instanceof ParboiledFilterSpecifier)) {
      return false;
    }
    return Objects.equals(_ast, ((ParboiledFilterSpecifier) o)._ast);
  }

  @Override
  public int hashCode() {
    return Objects.hash(_ast);
  }

  @Override
  public Set<IpAccessList> resolve(String node, SpecifierContext ctxt) {
    return _ast.accept(new FilterAstNodeToFilters(node, ctxt));
  }
}
