//! Closed Cargo.lock v4 subset for the fixed artifact-root dependency graph.
//! The caller prepays bounded parse/storage/comparison work before entry.
#[derive(Debug, Eq, PartialEq)]
struct Package {
    name: String,
    version: String,
    source: Option<String>,
    checksum: Option<String>,
    dependencies: Vec<String>,
}
fn quoted(value: &str) -> Result<String, ()> {
    let value: String = serde_json::from_str(value).map_err(|_| ())?;
    if value.is_empty() || value.len() > 512 || value.chars().any(char::is_control) { return Err(()); }
    Ok(value)
}
fn parse(bytes: &[u8]) -> Result<Vec<Package>, ()> {
    if bytes.len() > 1024 * 1024 { return Err(()); }
    let text = std::str::from_utf8(bytes).map_err(|_| ())?;
    let mut packages = Vec::new();
    let mut current: Option<Package> = None;
    let mut fields = 0u8;
    let mut dependencies = false;
    let mut version = false;
    for line in text.lines().map(str::trim) {
        if line.is_empty() || line.starts_with('#') { continue; }
        if dependencies {
            if line == "]" { dependencies = false; continue; }
            let dependency = quoted(line.strip_suffix(',').ok_or(())?)?;
            let package = current.as_mut().ok_or(())?;
            if package.dependencies.len() >= 256 || package.dependencies.contains(&dependency) { return Err(()); }
            package.dependencies.push(dependency);
            continue;
        }
        if line == "[[package]]" {
            if let Some(package) = current.take() {
                if fields & 3 != 3 { return Err(()); }
                packages.push(package);
            }
            if !version || packages.len() >= 256 { return Err(()); }
            current = Some(Package { name: String::new(), version: String::new(), source: None, checksum: None, dependencies: Vec::new() });
            fields = 0;
            continue;
        }
        let (key, value) = line.split_once('=').ok_or(())?;
        let (key, value) = (key.trim(), value.trim());
        let Some(package) = current.as_mut() else {
            if key != "version" || value != "4" || version { return Err(()); }
            version = true; continue;
        };
        let bit = match key {
            "name" => { package.name = quoted(value)?; 1 }
            "version" => { package.version = quoted(value)?; 2 }
            "source" => { package.source = Some(quoted(value)?); 4 }
            "checksum" => { package.checksum = Some(quoted(value)?); 8 }
            "dependencies" if value == "[" => { dependencies = true; 16 }
            _ => return Err(()),
        };
        if fields & bit != 0 { return Err(()); }
        fields |= bit;
    }
    if dependencies || !version { return Err(()); }
    if let Some(package) = current {
        if fields & 3 != 3 { return Err(()); }
        packages.push(package);
    }
    for (index, package) in packages.iter().enumerate() {
        // This supported graph has one version per name. Ambiguous dependency
        // spelling or a future graph requiring disambiguation must refuse.
        if packages[..index].iter().any(|p| p.name == package.name) { return Err(()); }
        if package.dependencies.iter().any(|d| !packages.iter().any(|p| p.name == *d)) { return Err(()); }
    }
    Ok(packages)
}
fn expected_dependencies(package: &Package) -> Vec<String> {
    let mut dependencies: Vec<_> = package.dependencies.iter()
        .filter(|d| package.name != "ash" || d.as_str() != "ash-foreign-adapter")
        .cloned().collect();
    dependencies.sort(); dependencies
}
/// Admit only pinned original registry packages/edges plus the fixed root and
/// dependency-free leaf. Workspace dev adapters and unrelated packages refuse.
pub(super) fn validate(original: &[u8], settled: &[u8]) -> Result<(), ()> {
    let original = parse(original)?;
    let settled = parse(settled)?;
    let ash = original.iter().find(|p| p.name == "ash").ok_or(())?;
    let mut root_dependencies = expected_dependencies(ash);
    root_dependencies.extend(["ash-checked-owner-leaf".into(), "ash-trusted-preparation".into()]);
    root_dependencies.sort();
    for package in &settled {
        if matches!(package.name.as_str(), "ash-checked-owner-root" | "ash-checked-owner-leaf") {
            if package.version != "0.0.0" || package.source.is_some() || package.checksum.is_some() { return Err(()); }
            let mut actual = package.dependencies.clone(); actual.sort();
            if package.name == "ash-checked-owner-root" {
                if actual != root_dependencies { return Err(()); }
            } else if !actual.is_empty() { return Err(()); }
            continue;
        }
        if matches!(package.name.as_str(), "ash-foreign-adapter" | "xtask") { return Err(()); }
        let expected = original.iter().find(|p| p.name == package.name).ok_or(())?;
        let mut actual = package.dependencies.clone(); actual.sort();
        if package.version != expected.version || package.source != expected.source
            || package.checksum != expected.checksum || actual != expected_dependencies(expected) { return Err(()); }
        if !matches!(package.name.as_str(), "ash" | "ash-trusted-preparation")
            && (package.source.as_deref() != Some("registry+https://github.com/rust-lang/crates.io-index")
                || package.checksum.as_ref().is_none_or(|s| s.len() != 64 || !s.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)))) { return Err(()); }
    }
    let root = settled.iter().position(|p| p.name == "ash-checked-owner-root").ok_or(())?;
    let mut reached = vec![false; settled.len()];
    let mut pending = vec![root];
    while let Some(index) = pending.pop() {
        if reached[index] { continue; }
        reached[index] = true;
        for dependency in &settled[index].dependencies {
            let next = settled.iter().position(|p| p.name == *dependency).ok_or(())?;
            if !reached[next] { pending.push(next); }
        }
    }
    if reached.iter().any(|reached| !reached) { return Err(()); }
    Ok(())
}

#[cfg(test)]
pub(super) fn fixture(original: &[u8]) -> Vec<u8> {
    // Test-only DATA graph derived from the original lock, not a claim that
    // Cargo resolved or compiled this generated project.
    let mut packages = parse(original).unwrap();
    let root_dependencies = {
        let ash = packages.iter().find(|p| p.name == "ash").unwrap();
        let mut dependencies = expected_dependencies(ash);
        dependencies.extend(["ash-checked-owner-leaf".into(), "ash-trusted-preparation".into()]);
        dependencies.sort(); dependencies
    };
    for package in &mut packages { package.dependencies = expected_dependencies(package); }
    packages.retain(|p| !matches!(p.name.as_str(),"ash-foreign-adapter"|"xtask"));
    packages.push(Package { name:"ash-checked-owner-root".into(),version:"0.0.0".into(),source:None,checksum:None,dependencies:root_dependencies });
    packages.push(Package { name:"ash-checked-owner-leaf".into(),version:"0.0.0".into(),source:None,checksum:None,dependencies:Vec::new() });
    let mut reached=std::collections::BTreeSet::new();
    let mut pending=vec!["ash-checked-owner-root".to_string()];
    while let Some(name)=pending.pop() {
        if !reached.insert(name.clone()) { continue; }
        pending.extend(packages.iter().find(|p| p.name==name).unwrap().dependencies.clone());
    }
    let mut output="version = 4\n".to_string();
    for p in packages.into_iter().filter(|p| reached.contains(&p.name)) {
        output.push_str(&format!("\n[[package]]\nname = {:?}\nversion = {:?}\n",p.name,p.version));
        if let Some(source)=p.source { output.push_str(&format!("source = {source:?}\n")); }
        if let Some(checksum)=p.checksum { output.push_str(&format!("checksum = {checksum:?}\n")); }
        if !p.dependencies.is_empty() {
            output.push_str("dependencies = [\n");
            for dependency in p.dependencies { output.push_str(&format!(" {dependency:?},\n")); }
            output.push_str("]\n");
        }
    }
    output.into_bytes()
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn closed_graph_refuses_unknown_packages_edges_sources_and_versions() {
        let original=include_bytes!("../../Cargo.lock");
        let canonical=fixture(original);
        assert_eq!(validate(original,&canonical),Ok(()));
        let text=String::from_utf8(canonical).unwrap();
        for donor in [
            text.replacen("version = 4","version = 3",1),
            text.replacen("crates.io-index","donor-index",1),
            text.replacen("name = \"sha2\"","name = \"donor\"",1),
            text.replacen(" \"ash-trusted-preparation\","," \"ash-foreign-adapter\",",1),
            format!("{text}\n[[package]]\nname = \"unreachable\"\nversion = \"0\"\n"),
        ] { assert_ne!(donor,text); assert_eq!(validate(original,donor.as_bytes()),Err(())); }
    }
}
