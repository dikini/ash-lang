//! Written source-resource selectors only; no lifecycle or native authority.

use super::{
    ConcreteElement, ConcreteNode, Kind, NodeKind, SourceFile, Span, Token, TokenKind,
    TypeWorkBudget, ValidationError, charge, name, original_span, push, registry, same_name, text,
};
use crate::{
    resolved::{ResolvedTypeVariable, SourceResourceHost, SourceResourceTypeFact},
    surface::{SurfaceResourceReportCodec, SurfaceResourceReportCodecKind},
};

#[derive(Debug)]
pub(super) struct ResourceSelectors {
    pub(super) name: Span,
    formals: Vec<Span>,
    host: Option<Span>,
    codec: SurfaceResourceReportCodec,
}

impl ResourceSelectors {
    pub(super) fn from_node(
        node: &ConcreteNode,
        tokens: &[Token],
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ValidationError> {
        let mut formals = Vec::new();
        let mut host = None;
        let mut codec = None;
        let mut parameters_seen = false;
        for child in &node.children {
            charge(work, 1)?;
            let ConcreteElement::Node(child) = child else {
                continue;
            };
            if child.kind == NodeKind::TypeParameters {
                if parameters_seen {
                    return Err(registry());
                }
                parameters_seen = true;
                for formal in &child.children {
                    charge(work, 1)?;
                    if let ConcreteElement::Node(formal) = formal
                        && formal.kind == NodeKind::TypeParameter
                    {
                        push(&mut formals, name(formal, tokens, work)?, work)?;
                    }
                }
            } else if child.kind == NodeKind::SourceResourceField {
                let mut head = None;
                let mut second = None;
                for field in &child.children {
                    charge(work, 1)?;
                    if let ConcreteElement::Token(index) = field {
                        let token = tokens.get(*index).ok_or_else(registry)?;
                        if head.is_none() {
                            head = Some(token);
                        } else if second.is_none() {
                            second = Some(token);
                        }
                    }
                }
                match head.map(|token| &token.kind) {
                    Some(TokenKind::Identifier(word)) if word == "host" => {
                        let token = second.ok_or_else(registry)?;
                        if !matches!(token.kind, TokenKind::UpperIdentifier(_))
                            || host.replace(token.span).is_some()
                        {
                            return Err(registry());
                        }
                    }
                    Some(TokenKind::Identifier(word)) if word == "codec" => {
                        let token = second.ok_or_else(registry)?;
                        let kind = match &token.kind {
                            TokenKind::Identifier(word) if word == "scope" => {
                                SurfaceResourceReportCodecKind::Scope
                            }
                            TokenKind::Identifier(word) if word == "acquired_only" => {
                                SurfaceResourceReportCodecKind::AcquiredOnly
                            }
                            TokenKind::Identifier(word) if word == "checked_scope" => {
                                SurfaceResourceReportCodecKind::CheckedScope
                            }
                            _ => return Err(registry()),
                        };
                        if codec
                            .replace(SurfaceResourceReportCodec {
                                kind,
                                span: token.span,
                            })
                            .is_some()
                        {
                            return Err(registry());
                        }
                    }
                    _ => {}
                }
            }
        }
        if !parameters_seen {
            return Err(registry());
        }
        Ok(Self {
            name: name(node, tokens, work)?,
            formals,
            host,
            codec: codec.ok_or_else(registry)?,
        })
    }

    pub(super) fn authenticate(
        &self,
        source: &SourceFile,
        fact: &SourceResourceTypeFact,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        self.authenticate_fields(source, fact.host, &fact.parameters, fact.codec, work)
    }

    fn authenticate_fields(
        &self,
        source: &SourceFile,
        host: Option<SourceResourceHost>,
        parameters: &[ResolvedTypeVariable],
        codec: SurfaceResourceReportCodec,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        charge(work, 2)?;
        if codec != self.codec || parameters.len() != self.formals.len() {
            return Err(registry());
        }
        let spelling = match codec.kind {
            SurfaceResourceReportCodecKind::Scope => "scope",
            SurfaceResourceReportCodecKind::AcquiredOnly => "acquired_only",
            SurfaceResourceReportCodecKind::CheckedScope => "checked_scope",
        };
        if !same_name(source, codec.span, spelling, work)? {
            return Err(registry());
        }
        match (self.host, host) {
            (None, None) => Ok(()),
            (Some(selector), Some(host)) if selector == host.span => {
                let selected_name = text(source, selector)?;
                let mut selected = None;
                for (position, formal) in self.formals.iter().copied().enumerate() {
                    let formal_name = text(source, formal)?;
                    charge(work, 1 + formal_name.len() + selected_name.len())?;
                    if formal_name == selected_name
                        && selected.replace((position, formal)).is_some()
                    {
                        return Err(registry());
                    }
                }
                let (position, formal) = selected.ok_or_else(registry)?;
                let parameter = parameters.get(position).ok_or_else(registry)?;
                charge(work, 2)?;
                if host.position != position
                    || parameter.kind != Kind::Type
                    || original_span(&parameter.origin, work)? != formal
                    || !same_name(source, formal, &parameter.spelling, work)?
                {
                    return Err(registry());
                }
                Ok(())
            }
            _ => Err(registry()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{module::ModuleRoots, resolved::CheckedModule, types::TypeWorkBudget};
    use std::sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    };

    fn fixture(checked: bool) -> (SourceFile, Arc<SourceResourceTypeFact>) {
        static IDS: AtomicU64 = AtomicU64::new(0);
        let directory = std::env::temp_dir().join(format!(
            "ash-resource-selectors-{}-{}",
            std::process::id(),
            IDS.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&directory).unwrap();
        let original = if checked {
            include_str!("../../../../tests/fixtures/checked-owner-lifecycle/owner.ash")
                .split("pub run :")
                .next()
                .unwrap()
                .replace("Probe<H, R>", "Probe<H, Other, R>")
        } else {
            include_str!("../../../../tests/fixtures/source-owner/owner.ash").to_owned()
        };
        std::fs::write(directory.join("entry.ash"), original).unwrap();
        let graph =
            crate::module::load_module_graph(&directory.join("entry.ash"), &ModuleRoots::empty())
                .unwrap();
        std::fs::remove_dir_all(&directory).unwrap();
        let mut modules = Vec::<CheckedModule>::new();
        for loaded in graph.modules() {
            let dependencies = loaded
                .dependencies()
                .iter()
                .map(|edge| {
                    crate::resolve::DependencyExports::new(
                        edge,
                        modules
                            .iter()
                            .find(|module| module.module() == edge.target())
                            .unwrap()
                            .exports(),
                    )
                    .unwrap()
                })
                .collect::<Vec<_>>();
            let resolved = if checked {
                crate::resolve::resolve_checked_foreign_module(loaded, &dependencies)
            } else {
                crate::resolve::resolve_module(loaded, &dependencies)
            }
            .expect("real selector fixture resolves before independent coordinate checking");
            if loaded.id() == graph.entry() {
                return (
                    loaded.source().clone(),
                    Arc::clone(&resolved.source_resources()[0].header),
                );
            }
            modules.push(crate::elaborate::check_module(resolved).unwrap());
        }
        panic!("entry source resource");
    }

    fn coordinates(source: &SourceFile) -> ResourceSelectors {
        let parsed = super::super::syntax(source, &mut TypeWorkBudget::default()).unwrap();
        let root = parsed.root().unwrap();
        let node = root
            .children
            .iter()
            .find_map(|element| match element {
                ConcreteElement::Node(node) if node.kind == NodeKind::ResourceDefinition => {
                    Some(node)
                }
                _ => None,
            })
            .unwrap();
        ResourceSelectors::from_node(node, parsed.tokens(), &mut TypeWorkBudget::default()).unwrap()
    }

    fn assert_registry(result: Result<(), ValidationError>) {
        assert_eq!(
            result.unwrap_err().reason(),
            super::super::ValidationReason::Registry
        );
    }

    #[test]
    fn checked_resource_selectors_reject_coordinated_same_kind_and_source_claims() {
        let (source, fact) = fixture(true);
        let coordinates = coordinates(&source);
        coordinates
            .authenticate(&source, &fact, &mut TypeWorkBudget::default())
            .unwrap();
        let host = fact.host.unwrap();
        assert_eq!(fact.parameters[1].spelling, "Other");
        assert_eq!(fact.parameters[0].kind, fact.parameters[1].kind);
        let check = |host, parameters: &[ResolvedTypeVariable], codec| {
            coordinates.authenticate_fields(
                &source,
                host,
                parameters,
                codec,
                &mut TypeWorkBudget::default(),
            )
        };
        assert_registry(check(None, &fact.parameters, fact.codec));
        assert_registry(check(
            Some(SourceResourceHost {
                position: 1,
                ..host
            }),
            &fact.parameters,
            fact.codec,
        ));
        assert_registry(check(
            Some(SourceResourceHost {
                span: fact.parameters[0].origin.primary_span(),
                ..host
            }),
            &fact.parameters,
            fact.codec,
        ));
        let mut parameters = fact.parameters.to_vec();
        parameters[0].origin = parameters[1].origin.clone();
        assert_registry(check(Some(host), &parameters, fact.codec));
        let mut parameters = fact.parameters.to_vec();
        parameters[0].spelling = parameters[1].spelling.clone();
        assert_registry(check(Some(host), &parameters, fact.codec));
        assert_registry(check(
            Some(host),
            &fact.parameters,
            SurfaceResourceReportCodec {
                kind: SurfaceResourceReportCodecKind::Scope,
                ..fact.codec
            },
        ));
        assert_registry(check(
            Some(host),
            &fact.parameters,
            SurfaceResourceReportCodec {
                span: host.span,
                ..fact.codec
            },
        ));
        let donor = SourceFile::new("donor.ash", source.text()).unwrap();
        assert_registry(coordinates.authenticate(&donor, &fact, &mut TypeWorkBudget::default()));
        // The unchanged parsed coordinates are not a completed semantic proof.
        coordinates
            .authenticate(&source, &fact, &mut TypeWorkBudget::default())
            .unwrap();
    }

    #[test]
    fn checked_resource_selectors_preserve_absent_legacy_host() {
        let (source, fact) = fixture(false);
        let coordinates = coordinates(&source);
        assert!(fact.host.is_none());
        coordinates
            .authenticate(&source, &fact, &mut TypeWorkBudget::default())
            .unwrap();
        assert_registry(coordinates.authenticate_fields(
            &source,
            Some(SourceResourceHost {
                position: 0,
                span: fact.parameters[0].origin.primary_span(),
            }),
            &fact.parameters,
            fact.codec,
            &mut TypeWorkBudget::default(),
        ));
        assert_registry(coordinates.authenticate_fields(
            &source,
            None,
            &fact.parameters,
            SurfaceResourceReportCodec {
                kind: SurfaceResourceReportCodecKind::AcquiredOnly,
                ..fact.codec
            },
            &mut TypeWorkBudget::default(),
        ));
    }

    #[test]
    fn checked_resource_selectors_have_exact_prefix_spent_and_fresh_limits() {
        let (source, fact) = fixture(true);
        let coordinates = coordinates(&source);
        let mut measured = TypeWorkBudget::default();
        coordinates
            .authenticate(&source, &fact, &mut measured)
            .unwrap();
        let cost = measured.used();
        assert!(cost > 0);
        for prefix in [0, 7] {
            let mut exact = TypeWorkBudget::with_limit(prefix + cost);
            exact.charge(prefix).unwrap();
            coordinates
                .authenticate(&source, &fact, &mut exact)
                .unwrap();
            assert_eq!(exact.used(), prefix + cost);
            assert_eq!(
                coordinates
                    .authenticate(&source, &fact, &mut exact)
                    .unwrap_err()
                    .reason(),
                super::super::ValidationReason::Resource
            );
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            assert_eq!(
                coordinates
                    .authenticate(&source, &fact, &mut short)
                    .unwrap_err()
                    .reason(),
                super::super::ValidationReason::Resource
            );
        }
        coordinates
            .authenticate(&source, &fact, &mut TypeWorkBudget::with_limit(cost))
            .unwrap();
    }
}
