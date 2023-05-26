use vuln_reach::javascript::package::Package;

// https://registry.npmjs.org/mongoose/-/mongoose-7.2.1.tgz
// https://registry.npmjs.org/codemirror/-/codemirror-5.5.0.tgz
const PACKAGE_URI: &str = "https://registry.npmjs.org/codemirror/-/codemirror-5.5.0.tgz";

#[tokio::main]
async fn main() {
    let tarball = reqwest::get(PACKAGE_URI).await.unwrap().bytes().await.unwrap();

    let start = std::time::Instant::now();
    let package = Package::from_tarball_bytes(tarball.to_vec()).unwrap();
    println!("{:?}", start.elapsed());
}
