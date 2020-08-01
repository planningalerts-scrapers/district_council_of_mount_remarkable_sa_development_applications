// Parses the development applications at the South Australian District Council of Mount Remarkable
// web site and places them in a database.
//
// Michael Bone
// 9th March 2019
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
const fs = require("fs");
const cheerio = require("cheerio");
const request = require("request-promise-native");
const sqlite3 = require("sqlite3");
const urlparser = require("url");
const moment = require("moment");
const pdfjs = require("pdfjs-dist");
const didyoumean2_1 = require("didyoumean2"), didyoumean = didyoumean2_1;
sqlite3.verbose();
const DevelopmentApplicationsUrl = "https://www.mtr.sa.gov.au/documents/district-council-of-mount-remarkable6";
const CommentUrl = "mailto:postmaster@mtr.sa.gov.au";
// All valid street names, street suffixes, suburb names and hundred names.
let StreetNames = null;
let StreetSuffixes = null;
let SuburbNames = null;
let HundredNames = null;
// Two points that are less than the tolerance apart will be considered the same point.
const Tolerance = 3;
// Sets up an sqlite database.
async function initializeDatabase() {
    return new Promise((resolve, reject) => {
        let database = new sqlite3.Database("data.sqlite");
        database.serialize(() => {
            database.run("create table if not exists [data] ([council_reference] text primary key, [address] text, [description] text, [info_url] text, [comment_url] text, [date_scraped] text, [date_received] text)");
            resolve(database);
        });
    });
}
// Inserts a row in the database if the row does not already exist.
async function insertRow(database, developmentApplication) {
    return new Promise((resolve, reject) => {
        let sqlStatement = database.prepare("insert or replace into [data] values (?, ?, ?, ?, ?, ?, ?)");
        sqlStatement.run([
            developmentApplication.applicationNumber,
            developmentApplication.address,
            developmentApplication.description,
            developmentApplication.informationUrl,
            developmentApplication.commentUrl,
            developmentApplication.scrapeDate,
            developmentApplication.receivedDate
        ], function (error, row) {
            if (error) {
                console.error(error);
                reject(error);
            }
            else {
                console.log(`    Saved application \"${developmentApplication.applicationNumber}\" with address \"${developmentApplication.address}\", description \"${developmentApplication.description}\" and received date \"${developmentApplication.receivedDate}\" to the database.`);
                sqlStatement.finalize(); // releases any locks
                resolve(row);
            }
        });
    });
}
// Constructs a rectangle based on the intersection of the two specified rectangles.
function intersectRectangles(rectangle1, rectangle2) {
    let x1 = Math.max(rectangle1.x, rectangle2.x);
    let y1 = Math.max(rectangle1.y, rectangle2.y);
    let x2 = Math.min(rectangle1.x + rectangle1.width, rectangle2.x + rectangle2.width);
    let y2 = Math.min(rectangle1.y + rectangle1.height, rectangle2.y + rectangle2.height);
    if (x2 >= x1 && y2 >= y1)
        return { x: x1, y: y1, width: x2 - x1, height: y2 - y1 };
    else
        return { x: 0, y: 0, width: 0, height: 0 };
}
// Finds the intersection point of two lines.
function intersectLines(line1, line2) {
    if ((line1.x1 === line1.x2 && line1.y1 === line1.y2) || (line2.x1 === line2.x2 && line2.y1 === line2.y2))
        return undefined; // ignore zero length lines
    let denominator = (line2.y2 - line2.y1) * (line1.x2 - line1.x1) - (line1.x2 - line1.x1) * (line1.y2 - line1.y1);
    if (denominator === 0)
        return undefined; // ignore parallel lines
    let distance1 = ((line2.x2 - line2.x1) * (line1.y1 - line2.y1) - (line2.y2 - line2.y1) * (line1.x1 - line2.x1)) / denominator;
    let distance2 = ((line1.x2 - line1.x1) * (line1.y1 - line2.y1) - (line1.y2 - line1.y1) * (line1.x1 - line2.x1)) / denominator;
    if (distance1 < 0 || distance1 > 1 || distance2 < 0 || distance2 > 1) // check that the intersection is within the line segements
        return undefined;
    let x = line1.x1 + distance1 * (line1.x2 - line1.x1);
    let y = line1.y1 + distance1 * (line1.y2 - line1.y1);
    return { x: x, y: y };
}
// Rotates a rectangle 90 degrees clockwise about the origin.
function rotate90Clockwise(rectangle) {
    let x = -(rectangle.y + rectangle.height);
    let y = rectangle.x;
    let width = rectangle.height;
    let height = rectangle.width;
    rectangle.x = x;
    rectangle.y = y;
    rectangle.width = width;
    rectangle.height = height;
}
// Rotates a rectangle 90 degrees anti-clockwise about the origin.
function rotate90AntiClockwise(rectangle) {
    let x = rectangle.y;
    let y = -(rectangle.x + rectangle.width);
    let width = rectangle.height;
    let height = rectangle.width;
    rectangle.x = x;
    rectangle.y = y;
    rectangle.width = width;
    rectangle.height = height;
}
// Calculates the fraction of an element that lies within a cell (as a percentage).  For example,
// if a quarter of the specifed element lies within the specified cell then this would return 25.
function getPercentageOfElementInCell(element, cell) {
    let elementArea = getArea(element);
    let intersectionArea = getArea(intersectRectangles(cell, element));
    return (elementArea === 0) ? 0 : ((intersectionArea * 100) / elementArea);
}
// Calculates the area of a rectangle.
function getArea(rectangle) {
    return rectangle.width * rectangle.height;
}
// Gets the percentage of horizontal overlap between two rectangles (0 means no overlap and 100
// means 100% overlap).
function getHorizontalOverlapPercentage(rectangle1, rectangle2) {
    if (rectangle1 === undefined || rectangle2 === undefined)
        return 0;
    let startX1 = rectangle1.x;
    let endX1 = rectangle1.x + rectangle1.width;
    let startX2 = rectangle2.x;
    let endX2 = rectangle2.x + rectangle2.width;
    if (startX1 >= endX2 || endX1 <= startX2 || rectangle1.width === 0 || rectangle2.width === 0)
        return 0;
    let intersectionWidth = Math.min(endX1, endX2) - Math.max(startX1, startX2);
    let unionWidth = Math.max(endX1, endX2) - Math.min(startX1, startX2);
    return (intersectionWidth * 100) / unionWidth;
}
// Examines all the lines in a page of a PDF and constructs cells (ie. rectangles) based on those
// lines.
async function parseCells(page, useRectangles) {
    let operators = await page.getOperatorList();
    // Find the lines.  Each line is actually constructed using a rectangle with a very short
    // height or a very narrow width.
    let lines = [];
    let previousRectangle = undefined;
    let transformStack = [];
    let transform = [1, 0, 0, 1, 0, 0];
    transformStack.push(transform);
    for (let index = 0; index < operators.fnArray.length; index++) {
        let argsArray = operators.argsArray[index];
        // The following lists all drawing and text instructions in the PDF (this is useful for
        // troubleshooting purposes).
        console.log(`${Object.entries(pdfjs.OPS).find(pair => pair[1] === operators.fnArray[index])} ${argsArray}`);
        if (operators.fnArray[index] === pdfjs.OPS.restore)
            transform = transformStack.pop();
        else if (operators.fnArray[index] === pdfjs.OPS.save)
            transformStack.push(transform);
        else if (operators.fnArray[index] === pdfjs.OPS.transform)
            transform = pdfjs.Util.transform(transform, argsArray);
        else if (operators.fnArray[index] === pdfjs.OPS.constructPath) {
            if (useRectangles) { // older PDFs use this approach to construct lines
                let argumentIndex = 0;
                for (let operationIndex = 0; operationIndex < argsArray[0].length; operationIndex++) {
                    if (argsArray[0][operationIndex] === pdfjs.OPS.moveTo) // moveTo = 13
                        argumentIndex += 2;
                    else if (argsArray[0][operationIndex] === pdfjs.OPS.lineTo) // lineTo = 14
                        argumentIndex += 2;
                    else if (argsArray[0][operationIndex] === pdfjs.OPS.rectangle) { // rectangle = 19
                        let x1 = argsArray[1][argumentIndex++];
                        let y1 = argsArray[1][argumentIndex++];
                        let width = argsArray[1][argumentIndex++];
                        let height = argsArray[1][argumentIndex++];
                        let x2 = x1 + width;
                        let y2 = y1 + height;
                        [x1, y1] = pdfjs.Util.applyTransform([x1, y1], transform);
                        [x2, y2] = pdfjs.Util.applyTransform([x2, y2], transform);
                        width = x2 - x1;
                        height = y2 - y1;
                        previousRectangle = { x: x1, y: y1, width: width, height: height };
                    }
                }
            }
            else { // newer PDFs use this approach to construct lines
                let x1 = undefined;
                let y1 = undefined;
                let x2 = undefined;
                let y2 = undefined;
                let argumentIndex = 0;
                for (let operationIndex = 0; operationIndex < argsArray[0].length; operationIndex++) {
                    if (argsArray[0][operationIndex] === pdfjs.OPS.moveTo) { // moveTo = 13
                        x1 = argsArray[1][argumentIndex++];
                        y1 = argsArray[1][argumentIndex++];
                    }
                    else if (argsArray[0][operationIndex] === pdfjs.OPS.lineTo) { // lineTo = 14
                        if ((argumentIndex % 8) === 4) { // the right-most, bottom-most index (ie. the diagonally opposite corner of the rectangle)
                            x2 = argsArray[1][argumentIndex++];
                            y2 = argsArray[1][argumentIndex++];
                        }
                        else {
                            argumentIndex += 2;
                        }
                    }
                    else if (argsArray[0][operationIndex] === pdfjs.OPS.closePath) { // closePath = 18
                        if (x1 === undefined || y1 === undefined)
                            console.log("    Ignoring the constructed path because the top, left co-ordinate is undefined.");
                        else if (x2 === undefined || y2 === undefined)
                            console.log(`    Ignoring the constructed path because the bottom, right co-ordinate is undefined (but the top, left co-ordindate is [${x1}, ${y1}]).`);
                        else {
                            [x1, y1] = pdfjs.Util.applyTransform([x1, y1], transform);
                            [x2, y2] = pdfjs.Util.applyTransform([x2, y2], transform);
                            let width = Math.abs(x2 - x1);
                            let height = Math.abs(y2 - y1);
                            lines.push({ x: x1, y: y1, width: width, height: height });
                            x1 = undefined;
                            y1 = undefined;
                            x2 = undefined;
                            y2 = undefined;
                        }
                    }
                }
            }
        }
        else if (useRectangles && previousRectangle !== undefined && (operators.fnArray[index] === pdfjs.OPS.fill || operators.fnArray[index] === pdfjs.OPS.eoFill)) {
            lines.push(previousRectangle);
            previousRectangle = undefined;
        }
        //        } else if (!useRectangles && previousRectangle !== undefined && operators.fnArray[index] === pdfjs.OPS.endPath) {
        //            lines.push(previousRectangle);
        //            previousRectangle = undefined;
        //        }
    }
    console.log(`Found ${lines.length} line(s).`);
    for (let line of lines)
        console.log(`DrawRectangle(e.Graphics, ${line.x}f, ${line.y}f, ${line.width}f, ${line.height}f);  // line segment`);
    // Determine all the horizontal lines and vertical lines that make up the grid.  The following
    // is careful to ignore the short lines and small rectangles that could make up vector images
    // outside of the grid (such as a logo).  Otherwise these short lines would cause problems due
    // to the additional cells that they would cause to be constructed later.
    let horizontalLines = [];
    let verticalLines = [];
    for (let line of lines) {
        if (line.height <= Tolerance && line.width >= 10) // a horizontal line
            horizontalLines.push(line);
        else if (line.width <= Tolerance && line.height >= 10) // a vertical line
            verticalLines.push(line);
    }
    let verticalLineComparer = (a, b) => (a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0);
    verticalLines.sort(verticalLineComparer);
    console.log(`Found ${verticalLines.length} vertical line(s).`);
    let horizontalLineComparer = (a, b) => (a.y > b.y) ? 1 : ((a.y < b.y) ? -1 : 0);
    horizontalLines.sort(horizontalLineComparer);
    console.log(`Found ${horizontalLines.length} horizontal line(s).`);
    // Add the start and end points of all lines.
    let points = [];
    for (let line of horizontalLines) {
        let point = { x: line.x, y: line.y };
        if (!points.some(otherPoint => (point.x - otherPoint.x) ** 2 + (point.y - otherPoint.y) ** 2 < Tolerance ** 2))
            points.push(point);
        point = { x: line.x + line.width, y: line.y };
        if (!points.some(otherPoint => (point.x - otherPoint.x) ** 2 + (point.y - otherPoint.y) ** 2 < Tolerance ** 2))
            points.push(point);
    }
    for (let line of verticalLines) {
        let point = { x: line.x, y: line.y };
        if (!points.some(otherPoint => (point.x - otherPoint.x) ** 2 + (point.y - otherPoint.y) ** 2 < Tolerance ** 2))
            points.push(point);
        point = { x: line.x, y: line.y + line.height };
        if (!points.some(otherPoint => (point.x - otherPoint.x) ** 2 + (point.y - otherPoint.y) ** 2 < Tolerance ** 2))
            points.push(point);
    }
    // Find all intersection points.
    for (let verticalLine of verticalLines) {
        for (let horizontalLine of horizontalLines) {
            let point = intersectLines({ x1: horizontalLine.x, y1: horizontalLine.y, x2: horizontalLine.x + horizontalLine.width, y2: horizontalLine.y }, { x1: verticalLine.x, y1: verticalLine.y, x2: verticalLine.x, y2: verticalLine.y + verticalLine.height });
            if (point !== undefined && !points.some(otherPoint => (point.x - otherPoint.x) ** 2 + (point.y - otherPoint.y) ** 2 < Tolerance ** 2))
                points.push(point); // add the intersection point
        }
    }
    // Construct cells based on the grid of points.
    let cells = [];
    for (let point of points) {
        // Find the next closest point in the X direction (moving across horizontally with
        // approximately the same Y co-ordinate).
        let closestRightPoint = points.reduce(((previous, current) => (Math.abs(current.y - point.y) < Tolerance && current.x > point.x && (previous === undefined || (current.x - point.x < previous.x - point.x))) ? current : previous), undefined);
        // Find the next closest point in the Y direction (moving down vertically with
        // approximately the same X co-ordinate).
        let closestDownPoint = points.reduce(((previous, current) => (Math.abs(current.x - point.x) < Tolerance && current.y > point.y && (previous === undefined || (current.y - point.y < previous.y - point.y))) ? current : previous), undefined);
        // Construct a rectangle from the found points.
        if (closestRightPoint !== undefined && closestDownPoint !== undefined)
            cells.push({ elements: [], x: point.x, y: point.y, width: closestRightPoint.x - point.x, height: closestDownPoint.y - point.y });
    }
    // Sort the cells by approximate Y co-ordinate and then by X co-ordinate.
    let cellComparer = (a, b) => (Math.abs(a.y - b.y) < Tolerance) ? ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)) : ((a.y > b.y) ? 1 : -1);
    cells.sort(cellComparer);
    return cells;
}
// Parses the text elements from a page of a PDF.
async function parseElements(page) {
    let textContent = await page.getTextContent();
    // Find all the text elements.
    let elements = textContent.items.map(item => {
        let transform = item.transform;
        // Work around the issue https://github.com/mozilla/pdf.js/issues/8276 (heights are
        // exaggerated).  The problem seems to be that the height value is too large in some
        // PDFs.  Provide an alternative, more accurate height value by using a calculation
        // based on the transform matrix.
        let workaroundHeight = Math.sqrt(transform[2] * transform[2] + transform[3] * transform[3]);
        let x = transform[4];
        let y = transform[5];
        let width = item.width;
        let height = workaroundHeight;
        return { text: item.str, x: x, y: y, width: width, height: height };
    });
    return elements;
}
// Formats (and corrects) an address.
function formatAddress(applicationNumber, address) {
    address = address.trim().replace(/[-–]+$/, "").replace(/\s\s+/g, " ").trim(); // remove trailing dashes and multiple white space characters
    if (address.replace(/[\s,0-]/g, "") === "" || address.startsWith("No Residential Address")) // ignores addresses such as "0 0, 0" and "-"
        return "";
    // Remove the comma in house numbers larger than 1000.  For example, the following addresses:
    //
    //     4,665 Princes HWY MENINGIE 5264
    //     11,287 Princes HWY SALT CREEK 5264
    //
    // would be converted to the following:
    //
    //     4665 Princes HWY MENINGIE 5264
    //     11287 Princes HWY SALT CREEK 5264
    if (/^\d,\d\d\d/.test(address))
        address = address.substring(0, 1) + address.substring(2);
    else if (/^\d\d,\d\d\d/.test(address))
        address = address.substring(0, 2) + address.substring(3);
    let tokens = address.split(" ");
    let postCode = undefined;
    let token = tokens.pop();
    if (token === undefined)
        return address;
    if (/^\d\d\d\d$/.test(token))
        postCode = token;
    else
        tokens.push(token);
    // Ensure that a state code is added before the post code if a state code is not present.
    let state = "SA";
    token = tokens.pop();
    if (token === undefined)
        return address;
    if (["ACT", "NSW", "NT", "QLD", "SA", "TAS", "VIC", "WA"].includes(token.toUpperCase()))
        state = token.toUpperCase();
    else
        tokens.push(token);
    // Construct a fallback address to be used if the suburb name cannot be determined later.
    let fallbackAddress = (postCode === undefined) ? address : [...tokens, state, postCode].join(" ").trim();
    // Pop tokens from the end of the array until a valid suburb name is encountered (allowing
    // for a few spelling errors).  Note that this starts by examining for longer matches
    // (consisting of four tokens) before examining shorter matches.  This approach ensures
    // that the following address:
    //
    //     2,800 Woods Well RD COLEBATCH 5266
    //
    // is correctly converted to the following address:
    //
    //     2800 WOODS WELL ROAD, COLEBATCH SA 5266
    //
    // rather than (incorrectly) to the following address (notice that the street name has "BELL"
    // instead of "WELL" because there actually is a street named "BELL ROAD").
    //
    //     2800 Woods BELL ROAD, COLEBATCH SA 5266
    //
    // This also allows for addresses that contain hundred names such as the following:
    //
    //     Sec 26 Hd Palabie
    //     Lot no 1, Standley Road, Sect 16, Hundred of Pygery
    let suburbName = undefined;
    let hasHundredName = false;
    for (let index = 4; index >= 1; index--) {
        let tryHundredName = tokens.slice(-index).join(" ").toUpperCase();
        if (tryHundredName.startsWith("HD OF ") || tryHundredName.startsWith("HUNDRED OF") || tryHundredName.startsWith("HD ") || tryHundredName.startsWith("HUNDRED ")) {
            tryHundredName = tryHundredName.replace(/^HD OF /, "").replace(/^HUNDRED OF /, "").replace(/^HD /, "").replace(/^HUNDRED /, "").trim();
            let hundredNameMatch = didyoumean2_1.default(tryHundredName, Object.keys(HundredNames), { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 1, trimSpaces: true });
            if (hundredNameMatch !== null) {
                hasHundredName = true;
                let suburbNames = HundredNames[hundredNameMatch];
                if (suburbNames.length === 1) { // if a unique suburb exists for the hundred then use that suburb
                    suburbName = SuburbNames[suburbNames[0]];
                    tokens.splice(-index, index); // remove elements from the end of the array
                }
                break;
            }
        }
    }
    // Only search for a suburb name if there was no hundred name (because a suburb name is
    // unlikely to appear before a hundred name).
    if (!hasHundredName) {
        for (let index = 4; index >= 1; index--) {
            let trySuburbName = tokens.slice(-index).join(" ");
            let suburbNameMatch = didyoumean2_1.default(trySuburbName, Object.keys(SuburbNames), { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 1, trimSpaces: true });
            if (suburbNameMatch !== null) {
                suburbName = SuburbNames[suburbNameMatch];
                tokens.splice(-index, index); // remove elements from the end of the array           
                break;
            }
        }
    }
    // Expand any street suffix (for example, this converts "ST" to "STREET").
    token = tokens.pop();
    if (token !== undefined) {
        token = token.trim().replace(/,+$/, "").trim(); // removes trailing commas
        let streetSuffix = StreetSuffixes[token.toUpperCase()];
        if (streetSuffix === undefined)
            streetSuffix = Object.values(StreetSuffixes).find(streetSuffix => streetSuffix === token.toUpperCase()); // the street suffix is already expanded
        if (streetSuffix === undefined)
            tokens.push(token); // unrecognised street suffix
        else
            tokens.push(streetSuffix); // add back the expanded street suffix
    }
    // Pop tokens from the end of the array until a valid street name is encountered (allowing
    // for a few spelling errors).  Similar to the examination of suburb names, this examines
    // longer matches before examining shorter matches (for the same reason).
    let streetName = undefined;
    for (let index = 5; index >= 1; index--) {
        let tryStreetName = tokens.slice(-index).join(" ").trim().replace(/,+$/, "").trim(); // allows for commas after the street name
        let streetNameMatch = didyoumean2_1.default(tryStreetName, Object.keys(StreetNames), { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 1, trimSpaces: true });
        if (streetNameMatch !== null) {
            streetName = streetNameMatch;
            let suburbNames = StreetNames[streetNameMatch];
            tokens.splice(-index, index); // remove elements from the end of the array           
            // If the suburb was not determined earlier then attempt to obtain the suburb based
            // on the street (ie. if there is only one suburb associated with the street).  For
            // example, this would automatically add the suburb to "22 Jefferson CT 5263",
            // producing the address "22 JEFFERSON COURT, WELLINGTON EAST SA 5263".
            if (suburbName === undefined && suburbNames.length === 1)
                suburbName = SuburbNames[suburbNames[0]];
            break;
        }
    }
    // If a post code was included in the original address then use it to override the post code
    // included in the suburb name (because the post code in the original address is more likely
    // to be correct).
    if (postCode !== undefined && suburbName !== undefined)
        suburbName = suburbName.replace(/\s+\d\d\d\d$/, " " + postCode);
    // Do not allow an address that does not have a suburb name.
    if (suburbName === undefined) {
        console.log(`Ignoring the development application "${applicationNumber}" because a suburb name could not be determined for the address: ${address}`);
        return "";
    }
    // Reconstruct the address with a comma between the street address and the suburb.
    if (suburbName === undefined || suburbName.trim() === "")
        address = fallbackAddress;
    else {
        if (streetName !== undefined && streetName.trim() !== "")
            tokens.push(streetName);
        let streetAddress = tokens.join(" ").trim().replace(/,+$/, "").trim(); // removes trailing commas
        address = streetAddress + (streetAddress === "" ? "" : ", ") + suburbName;
    }
    // Ensure that the address includes the state "SA".
    if (address !== "" && !/\bSA\b/g.test(address))
        address += " SA";
    return address;
}
// Parses a PDF document.
async function parsePdf(url, shouldRotate) {
    console.log(`Reading development applications from ${url}.`);
    let developmentApplications = [];
    // Read the PDF.
    let buffer = await request({ url: url, encoding: null, proxy: process.env.MORPH_PROXY });
    await sleep(2000 + getRandom(0, 5) * 1000);
    // Parse the PDF.  Each page has the details of multiple applications.
    let applicationNumberHeadingCell = undefined;
    let receivedDateHeadingCell = undefined;
    let addressHeadingCell = undefined;
    let descriptionHeadingCell = undefined;
    let pdf = await pdfjs.getDocument({ data: buffer, disableFontFace: true, ignoreErrors: true });
    for (let pageIndex = 0; pageIndex < pdf.numPages; pageIndex++) {
        console.log(`Reading and parsing applications from page ${pageIndex + 1} of ${pdf.numPages}.`);
        let page = await pdf.getPage(pageIndex + 1);
        // Construct cells (ie. rectangles) based on the horizontal and vertical line segments
        // in the PDF page.
        let cells = await parseCells(page, false);
        // Construct elements based on the text in the PDF page.
        let elements = await parseElements(page);
        // for (let cell of cells)
        //     console.log(`DrawRectangle(e.Graphics, ${cell.x}f, ${cell.y}f, ${cell.width}f, ${cell.height}f);`);
        for (let element of elements)
            console.log(`DrawText(e.Graphics, "${element.text.replace(/\"/g, "\"\"")}", ${element.x}f, ${element.y}f, ${element.width}f, ${element.height}f);`);
        if (page.rotate !== 0) // degrees
            console.log(`Page is rotated ${page.rotate}°.`);
        if (shouldRotate) {
            // Experimentally determined that the following rotation and translation correctly
            // aligns the grid lines with the text elements in some PDFs.
            console.log("Retrying with a rotation of 90°.");
            let viewport = await page.getViewport(1.0);
            for (let cell of cells) {
                rotate90AntiClockwise(cell);
                cell.y = cell.y + viewport.height; // experimentally determined translation
            }
        }
        // The co-ordinate system used in a PDF is typically "upside down" so invert the
        // co-ordinates (and so this makes the subsequent logic easier to understand).
        for (let cell of cells)
            cell.y = -(cell.y + cell.height);
        for (let element of elements)
            element.y = -(element.y + element.height);
        if (page.rotate !== 0) // degrees
            console.log(`Page is rotated ${page.rotate}°.`);
        if (page.rotate === 90) { // degrees
            for (let cell of cells)
                rotate90Clockwise(cell);
            for (let element of elements) {
                rotate90Clockwise(element);
                [element.y, element.width, element.height] = [element.y - element.width, element.height, element.width]; // artificial adjustment (based on experimentation)
            }
        }
        // Sort the elements by approximate Y co-ordinate and then by X co-ordinate.
        let cellComparer = (a, b) => (Math.abs(a.y - b.y) < Tolerance) ? ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)) : ((a.y > b.y) ? 1 : -1);
        cells.sort(cellComparer);
        console.log(`    Cell count: ${cells.length}`);
        // Sort the text elements by approximate Y co-ordinate and then by X co-ordinate.
        let elementComparer = (a, b) => (Math.abs(a.y - b.y) < Tolerance) ? ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)) : ((a.y > b.y) ? 1 : -1);
        elements.sort(elementComparer);
        console.log(`    Element count: ${elements.length}`);
        // Allocate each element to an "owning" cell.
        let ownedElementCount = 0;
        for (let element of elements) {
            let ownerCell = cells.find(cell => getPercentageOfElementInCell(element, cell) > 50); // at least 50% of the element must be within the cell deemed to be the owner
            if (ownerCell !== undefined) {
                ownerCell.elements.push(element);
                ownedElementCount++;
            }
        }
        console.log(`    Elements owned by cells count: ${ownedElementCount}`);
        // Group the cells into rows.
        let rows = [];
        for (let cell of cells) {
            let row = rows.find(row => Math.abs(row[0].y - cell.y) < Tolerance); // approximate Y co-ordinate match
            if (row === undefined)
                rows.push([cell]); // start a new row
            else
                row.push(cell); // add to an existing row
        }
        // Check that there is at least one row (even if it is just the heading row).
        if (rows.length === 0) {
            let elementSummary = elements.map(element => `[${element.text}]`).join("");
            console.log(`No development applications can be parsed from the current page because no rows were found (based on the grid).  Elements: ${elementSummary}`);
            continue;
        }
        // Ensure the rows are sorted by Y co-ordinate and that the cells in each row are sorted
        // by X co-ordinate (this is really just a safety precaution because the earlier sorting
        // of cells in the parseCells function should have already ensured this).
        let rowComparer = (a, b) => (a[0].y > b[0].y) ? 1 : ((a[0].y < b[0].y) ? -1 : 0);
        rows.sort(rowComparer);
        let rowCellComparer = (a, b) => (a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0);
        for (let row of rows)
            row.sort(rowCellComparer);
        // Find the heading cells.
        if (applicationNumberHeadingCell === undefined) {
            applicationNumberHeadingCell = cells.find(cell => /^(developmentnumber|developmentno\.|appno)/i.test(cell.elements.map(element => element.text).join("").replace(/\s/g, "")));
            receivedDateHeadingCell = cells.find(cell => /^(dateofapplication|dateofregistration|dateregistered)/i.test(cell.elements.map(element => element.text).join("").replace(/\s/g, "")));
            addressHeadingCell = cells.find(cell => /^(propertyaddress|locationofdevelopment)/i.test(cell.elements.map(element => element.text).join("").replace(/\s/g, "")));
            descriptionHeadingCell = cells.find(cell => /^(natureofdevelopment|descriptionofdev)/i.test(cell.elements.map(element => element.text).join("").replace(/\s/g, "")));
        }
        if (applicationNumberHeadingCell === undefined) {
            let elementSummary = elements.map(element => `[${element.text}]`).join("");
            console.log(`No development applications can be parsed from the current page because the "Development Number", Development No." or "App No" column heading was not found.  Elements: ${elementSummary}`);
            continue;
        }
        if (addressHeadingCell === undefined) {
            let elementSummary = elements.map(element => `[${element.text}]`).join("");
            console.log(`No development applications can be parsed from the current page because the "Property Address" or "Location of Development" column heading was not found.  Elements: ${elementSummary}`);
            continue;
        }
        // Try to extract a development application from each row (some rows, such as the heading
        // row, will not actually contain a development application).
        for (let row of rows) {
            let applicationNumberCell = row.find(cell => getHorizontalOverlapPercentage(cell, applicationNumberHeadingCell) > 90);
            let receivedDateCell = row.find(cell => getHorizontalOverlapPercentage(cell, receivedDateHeadingCell) > 90);
            let addressCell = row.find(cell => getHorizontalOverlapPercentage(cell, addressHeadingCell) > 90);
            let descriptionCell = row.find(cell => getHorizontalOverlapPercentage(cell, descriptionHeadingCell) > 90);
            // Construct the application number.
            if (applicationNumberCell === undefined) {
                let rowSummary = row.map(cell => `[${cell.elements.map(element => `(${element.text})`).join("")}]`).join("");
                console.log(`No application number was found on the row: ${rowSummary}`);
                continue;
            }
            let applicationNumber = applicationNumberCell.elements.map(element => element.text).join("").trim();
            if (!/[0-9]+\/[0-9]+\/[0-9]+/.test(applicationNumber)) { // an application number must be present, for example, "690/006/15"
                console.log(`Ignoring "${applicationNumber}" because it is not formatted as an application number.`);
                continue;
            }
            console.log(`Found development application ${applicationNumber}.`);
            // Construct the address.
            if (addressCell === undefined) {
                console.log(`Ignoring the development application "${applicationNumber}" because it has no address cell.`);
                continue;
            }
            let address = addressCell.elements.map(element => element.text).join(" ").replace(/\s\s+/g, " ").trim();
            address = formatAddress(applicationNumber, address);
            if (address === "") {
                console.log(`Ignoring the development application "${applicationNumber}" because it has no address.`);
                continue;
            }
            // Construct the description.
            let description = "";
            if (descriptionCell !== undefined)
                description = descriptionCell.elements.map(element => element.text).join(" ").replace(/\s\s+/g, " ").trim();
            // Construct the received date.
            let receivedDate = moment.invalid();
            if (receivedDateCell !== undefined && receivedDateCell.elements.length > 0)
                receivedDate = moment(receivedDateCell.elements.map(element => element.text).join("").replace(/\s\s+/g, " ").trim(), "D/MM/YYYY", true);
            developmentApplications.push({
                applicationNumber: applicationNumber,
                address: address,
                description: ((description === "") ? "No Description Provided" : description),
                informationUrl: url,
                commentUrl: CommentUrl,
                scrapeDate: moment().format("YYYY-MM-DD"),
                receivedDate: receivedDate.isValid() ? receivedDate.format("YYYY-MM-DD") : ""
            });
        }
    }
    return developmentApplications;
}
// Gets a random integer in the specified range: [minimum, maximum).
function getRandom(minimum, maximum) {
    return Math.floor(Math.random() * (Math.floor(maximum) - Math.ceil(minimum))) + Math.ceil(minimum);
}
// Pauses for the specified number of milliseconds.
function sleep(milliseconds) {
    return new Promise(resolve => setTimeout(resolve, milliseconds));
}
// Parses the development applications.
async function main() {
    // Ensure that the database exists.
    let database = await initializeDatabase();
    // Read the files containing all possible street names, street suffixes, suburb names and
    // hundred names.
    StreetNames = {};
    for (let line of fs.readFileSync("streetnames.txt").toString().replace(/\r/g, "").trim().split("\n")) {
        let streetNameTokens = line.toUpperCase().split(",");
        let streetName = streetNameTokens[0].trim();
        let suburbName = streetNameTokens[1].trim();
        (StreetNames[streetName] || (StreetNames[streetName] = [])).push(suburbName); // several suburbs may exist for the same street name
    }
    StreetSuffixes = {};
    for (let line of fs.readFileSync("streetsuffixes.txt").toString().replace(/\r/g, "").trim().split("\n")) {
        let streetSuffixTokens = line.toUpperCase().split(",");
        StreetSuffixes[streetSuffixTokens[0].trim()] = streetSuffixTokens[1].trim();
    }
    SuburbNames = {};
    for (let line of fs.readFileSync("suburbnames.txt").toString().replace(/\r/g, "").trim().split("\n")) {
        let suburbTokens = line.toUpperCase().split(",");
        SuburbNames[suburbTokens[0].trim()] = suburbTokens[1].trim();
    }
    HundredNames = {};
    for (let line of fs.readFileSync("hundrednames.txt").toString().replace(/\r/g, "").trim().split("\n")) {
        let hundredNameTokens = line.toUpperCase().split(",");
        HundredNames[hundredNameTokens[0].trim()] = hundredNameTokens[1].trim().split(";");
    }
    // Read the main page of development applications.
    console.log(`Retrieving page: ${DevelopmentApplicationsUrl}`);
    let body = await request({ url: DevelopmentApplicationsUrl, rejectUnauthorized: false, proxy: process.env.MORPH_PROXY });
    await sleep(2000 + getRandom(0, 5) * 1000);
    let $ = cheerio.load(body);
    let pdfUrls = [];
    for (let element of $("h4 a").get()) {
        let pdfUrl = new urlparser.URL(element.attribs.href, DevelopmentApplicationsUrl).href;
        if (pdfUrl.toLowerCase().includes(".pdf"))
            if (!pdfUrls.some(url => url === pdfUrl)) // avoid duplicates
                pdfUrls.unshift(pdfUrl);
    }
    // Always parse the most recent PDF file and randomly select one other PDF file to parse.
    if (pdfUrls.length === 0) {
        console.log("No PDF URLs were found on the page.");
        return;
    }
    console.log(`Found ${pdfUrls.length} PDF file(s).  Selecting two to parse.`);
    // Select the most recent PDF.  And randomly select one other PDF (avoid processing all PDFs
    // at once because this may use too much memory, resulting in morph.io terminating the current
    // process).
    let selectedPdfUrls = [];
    selectedPdfUrls.push(pdfUrls.pop());
    if (pdfUrls.length > 0)
        selectedPdfUrls.push(pdfUrls[getRandom(0, pdfUrls.length)]);
    if (getRandom(0, 2) === 0)
        selectedPdfUrls.reverse();
    console.log("Hard-coded the PDF for testing purposes.");
    selectedPdfUrls = ["https://www.mtr.sa.gov.au/__data/assets/pdf_file/0035/479393/6.-June-2020.pdf"];
    for (let pdfUrl of selectedPdfUrls) {
        console.log(`Parsing document: ${pdfUrl}`);
        let developmentApplications = await parsePdf(pdfUrl, false);
        //        if (developmentApplications.length === 0)
        //            developmentApplications = await parsePdf(pdfUrl, true);
        console.log(`Parsed ${developmentApplications.length} development ${(developmentApplications.length == 1) ? "application" : "applications"} from document: ${pdfUrl}`);
        // Attempt to avoid reaching 512 MB memory usage (this will otherwise result in the
        // current process being terminated by morph.io).
        if (global.gc)
            global.gc();
        console.log("Saving development applications to the database.");
        for (let developmentApplication of developmentApplications)
            await insertRow(database, developmentApplication);
    }
}
main().then(() => console.log("Complete.")).catch(error => console.error(error));
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoic2NyYXBlci5qcyIsInNvdXJjZVJvb3QiOiIiLCJzb3VyY2VzIjpbInNjcmFwZXIudHMiXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6IkFBQUEsbUdBQW1HO0FBQ25HLDBDQUEwQztBQUMxQyxFQUFFO0FBQ0YsZUFBZTtBQUNmLGlCQUFpQjtBQUVqQixZQUFZLENBQUM7O0FBRWIseUJBQXlCO0FBQ3pCLG1DQUFtQztBQUNuQyxrREFBa0Q7QUFDbEQsbUNBQW1DO0FBQ25DLGlDQUFpQztBQUNqQyxpQ0FBaUM7QUFDakMsb0NBQW9DO0FBQ3BDLHlFQUFzRDtBQUV0RCxPQUFPLENBQUMsT0FBTyxFQUFFLENBQUM7QUFFbEIsTUFBTSwwQkFBMEIsR0FBRywyRUFBMkUsQ0FBQztBQUMvRyxNQUFNLFVBQVUsR0FBRyxpQ0FBaUMsQ0FBQztBQUlyRCwyRUFBMkU7QUFFM0UsSUFBSSxXQUFXLEdBQUcsSUFBSSxDQUFDO0FBQ3ZCLElBQUksY0FBYyxHQUFHLElBQUksQ0FBQztBQUMxQixJQUFJLFdBQVcsR0FBRyxJQUFJLENBQUM7QUFDdkIsSUFBSSxZQUFZLEdBQUcsSUFBSSxDQUFDO0FBRXhCLHVGQUF1RjtBQUV2RixNQUFNLFNBQVMsR0FBRyxDQUFDLENBQUM7QUFFcEIsOEJBQThCO0FBRTlCLEtBQUssVUFBVSxrQkFBa0I7SUFDN0IsT0FBTyxJQUFJLE9BQU8sQ0FBQyxDQUFDLE9BQU8sRUFBRSxNQUFNLEVBQUUsRUFBRTtRQUNuQyxJQUFJLFFBQVEsR0FBRyxJQUFJLE9BQU8sQ0FBQyxRQUFRLENBQUMsYUFBYSxDQUFDLENBQUM7UUFDbkQsUUFBUSxDQUFDLFNBQVMsQ0FBQyxHQUFHLEVBQUU7WUFDcEIsUUFBUSxDQUFDLEdBQUcsQ0FBQyw4TEFBOEwsQ0FBQyxDQUFDO1lBQzdNLE9BQU8sQ0FBQyxRQUFRLENBQUMsQ0FBQztRQUN0QixDQUFDLENBQUMsQ0FBQztJQUNQLENBQUMsQ0FBQyxDQUFDO0FBQ1AsQ0FBQztBQUVELG1FQUFtRTtBQUVuRSxLQUFLLFVBQVUsU0FB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LEdBQUcsS0FBSyxDQUFDLEVBQUUsQ0FBQyxHQUFHLENBQUMsS0FBSyxDQUFDLEVBQUUsR0FBRyxLQUFLLENBQUMsRUFBRSxDQUFDLEdBQUcsQ0FBQyxLQUFLLENBQUMsRUFBRSxHQUFHLEtBQUssQ0FBQyxFQUFFLENBQUMsR0FBRyxDQUFDLEtBQUssQ0FBQyxFQUFFLEdBQUcsS0FBSyxDQUFDLEVBQUUsQ0FBQyxDQUFDO0lBQ2hILElBQUksV0FBVyxLQUFLLENBQUM7UUFDakIsT0FBTyxTQUFTLENBQUMsQ0FBRSx3QkFBd0I7SUFFL0MsSUFBSSxTQUFTLEdBQUcsQ0FBQyxDQUFDLEtBQUssQ0FBQyxFQUFFLEdBQUcsS0FBSyxDQUFDLEVBQUUsQ0FBQyxHQUFHLENBQUMsS0FBSyxDQUFDLEVBQUUsR0FBRyxLQUFLLENBQUMsRUFBRSxDQUFDLEdBQUcsQ0FBQyxLQUFLLENBQUMsRUFBRSxHQUFHLEtBQUssQ0FBQyxFQUFFLENBQUMsR0FBRyxDQUFDLEtBQUssQ0FBQyxFQUFFLEdBQUcsS0FBSyxDQUFDLEVBQUUsQ0FBQyxDQUFDLEdBQUcsV0FBVyxDQUFDO0lBQzlILElBQUksU0FBUyxHQUFHLENBQUMsQ0FBQyxLQUFLLENBQUMsRUFBRSxHQUFHLEtBQUssQ0FBQyxFQUFFLENBQUMsR0FBRyxDQUFDLEtBQUssQ0FBQyxFQUFFLEdBQUcsS0FBSyxDQUFDLEVBQUUsQ0FBQyxHQUFHLENBQUMsS0FBSyxDQUFDLEVBQUUsR0FBRyxLQUFLLENBQUMsRUFBRSxDQUFDLEdBQUcsQ0FBQyxLQUFLLENBQUMsRUFBRSxHQUFHLEtBQUssQ0FBQyxFQUFFLENBQUMsQ0FBQyxHQUFHLFdBQVcsQ0FBQztJQUM5SCxJQUFJLFNBQVMsR0FBRyxDQUFDLElBQUksU0FBUyxHQUFHLENBQUMsSUFBSSxTQUFTLEdBQUcsQ0FBQyxJQUFJLFNBQVMsR0FBRyxDQUFDLEVBQUcsMkRBQTJEO1FBQzlILE9BQU8sU0FBUyxDQUFDO0lBRXJCLElBQUksQ0FBQyxHQUFHLEtBQUssQ0FBQyxFQUFFLEdBQUcsU0FBUyxHQUFHLENBQUMsS0FBSyxDQUFDLEVBQUUsR0FBRyxLQUFLLENBQUMsRUFBRSxDQUFDLENBQUM7SUFDckQsSUFBSSxDQUFDLEdBQUcsS0FBSyxDQUFDLEVBQUUsR0FBRyxTQUFTLEdBQUcsQ0FBQyxLQUFLLENBQUMsRUFBRSxHQUFHLEtBQUssQ0FBQyxFQUFFLENBQUMsQ0FBQztJQUNyRCxPQUFPLEVBQUUsQ0FBQyxFQUFFLENBQUMsRUFBRSxDQUFDLEVBQUUsQ0FBQyxFQUFFLENBQUM7QUFDMUIsQ0FBQztBQUVELDZEQUE2RDtBQUU3RCxTQUFTLGlCQUFpQixDQUFDLFNBQW9CO0lBQzNDLElBQUksQ0FBQyxHQUFHLENBQUMsQ0FBQyxTQUFTLENBQUMsQ0FBQyxHQUFHLFNBQVMsQ0FBQyxNQUFNLENBQUMsQ0FBQztJQUMxQyxJQUFJLENBQUMsR0FBRyxTQUFTLENBQUMsQ0FBQyxDQUFDO0lBQ3BCLElBQUksS0FBSyxHQUFHLFNBQVMsQ0FBQyxNQUFNLENBQUM7SUFDN0IsSUFBSSxNQUFNLEdBQUcsU0FBUyxDQUFDLEtBQUssQ0FBQztJQUM3QixTQUFTLENBQUMsQ0FBQyxHQUFHLENBQUMsQ0FBQztJQUNoQixTQUFTLENBQUMsQ0FBQyxHQUFHLENBQUMsQ0FBQztJQUNoQixTQUFTLENBQUMsS0FBSyxHQUFHLEtBQUssQ0FBQztJQUN4QixTQUFTLENBQUMsTUFBTSxHQUFHLE1BQU0sQ0FBQztBQUM5QixDQUFDO0FBRUQsa0VBQWtFO0FBRWxFLFNBQVMscUJBQXFCLENBQUMsU0FBb0I7SUFDL0MsSUFBSSxDQUFDLEdBQUcsU0FBUyxDQUFDLENBQUMsQ0FBQztJQUNwQixJQUFJLENBQUMsR0FBRyxDQUFDLENBQUMsU0FBUyxDQUFDLENBQUMsR0FBRyxTQUFTLENBQUMsS0FBSyxDQUFDLENBQUM7SUFDekMsSUFBSSxLQUFLLEdBQUcsU0FBUyxDQUFDLE1BQU0sQ0FBQztJQUM3QixJQUFJLE1BQU0sR0FBRyxTQUFTLENBQUMsS0FBSyxDQUFDO0lBQzdCLFNBQVMsQ0FBQyxDQUFDLEdBQUcsQ0FBQyxDQUFDO0lBQ2hCLFNBQVMsQ0FBQyxDQUFDLEdBQUcsQ0FBQyxDQUFDO0lBQ2hCLFNBQVMsQ0FBQyxLQUFLLEdBQUcsS0FBSyxDQUFDO0lBQ3hCLFNBQVMsQ0FBQyxNQUFNLEdBQUcsTUFBTSxDQUFDO0FBQzlCLENBQUM7QUFFRCxpR0FBaUc7QUFDakcsaUdBQWlHO0FBRWpHLFNBQVMsNEJBQTRCLENBQUMsT0FBZ0IsRUFBRSxJQUFVO0lBQzlELElBQUksV0FBVyxHQUFHLE9BQU8sQ0FBQyxPQUFPLENBQUMsQ0FBQztJQUNuQyxJQUFJLGdCQUFnQixHQUFHLE9BQU8sQ0FBQyxtQkFBbUIsQ0FBQyxJQUFJLEVBQUUsT0FBTyxDQUFDLENBQUMsQ0FBQztJQUNuRSxPQUFPLENBQUMsV0FBVyxLQUFLLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxnQkFBZ0IsR0FBRyxHQUFHLENBQUMsR0FBRyxXQUFXLENBQUMsQ0FBQztBQUM5RSxDQUFDO0FBRUQsc0NBQXNDO0FBRXRDLFNBQVMsT0FBTyxDQUFDLFNBQW9CO0lBQ2pDLE9BQU8sU0FBUyxDQUFDLEtBQUssR0FBRyxTQUFTLENBQUMsTUFBTSxDQUFDO0FBQzlDLENBQUM7QUFFRCwrRkFBK0Y7QUFDL0YsdUJBQXVCO0FBRXZCLFNBQVMsOEJBQThCLENBQUMsVUFBcUIsRUFBRSxVQUFxQjtJQUNoRixJQUFJLFVBQVUsS0FBSyxTQUFTLElBQUksVUFBVSxLQUFLLFNBQVM7UUFDcEQsT0FBTyxDQUFDLENBQUM7SUFFYixJQUFJLE9BQU8sR0FBRyxVQUFVLENBQUMsQ0FBQyxDQUFDO0lBQzNCLElBQUksS0FBSyxHQUFHLFVBQVUsQ0FBQyxDQUFDLEdBQUcsVUFBVSxDQUFDLEtBQUssQ0FBQztJQUU1QyxJQUFJLE9BQU8sR0FBRyxVQUFVLENBQUMsQ0FBQyxDQUFDO0lBQzNCLElBQUksS0FBSyxHQUFHLFVBQVUsQ0FBQyxDQUFDLEdBQUcsVUFBVSxDQUFDLEtBQUssQ0FBQztJQUU1QyxJQUFJLE9BQU8sSUFBSSxLQUFLLElBQUksS0FBSyxJQUFJLE9BQU8sSUFBSSxVQUFVLENBQUMsS0FBSyxLQUFLLENBQUMsSUFBSSxVQUFVLENBQUMsS0FBSyxLQUFLLENBQUM7UUFDeEYsT0FBTyxDQUFDLENBQUM7SUFFYixJQUFJLGlCQUFpQixHQUFHLElBQUksQ0FBQyxHQUFHLENBQUMsS0FBSyxFQUFFLEtBQUssQ0FBQyxHQUFHLElBQUksQ0FBQyxHQUFHLENBQUMsT0FBTyxFQUFFLE9BQU8sQ0FBQyxDQUFDO0lBQzVFLElBQUksVUFBVSxHQUFHLElBQUksQ0FBQyxHQUFHLENBQUMsS0FBSyxFQUFFLEtBQUssQ0FBQyxHQUFHLElBQUksQ0FBQyxHQUFHLENBQUMsT0FBTyxFQUFFLE9BQU8sQ0FBQyxDQUFDO0lBRXJFLE9BQU8sQ0FBQyxpQkFBaUIsR0FBRyxHQUFHLENBQUMsR0FBRyxVQUFVLENBQUM7QUFDbEQsQ0FBQztBQUVELGlHQUFpRztBQUNqRyxTQUFTO0FBRVQsS0FBSyxVQUFVLFVBQVUsQ0FBQyxJQUFJLEVBQUUsYUFBc0I7SUFDbEQsSUFBSSxTQUFTLEdBQUcsTUFBTSxJQUFJLENBQUMsZUFBZSxFQUFFLENBQUM7SUFFN0MseUZBQXlGO0lBQ3pGLGlDQUFpQztJQUVqQyxJQUFJLEtBQUssR0FBZ0IsRUFBRSxDQUFDO0lBRTVCLElBQUksaUJBQWlCLEdBQUcsU0FBUyxDQUFDO0lBQ2xDLElBQUksY0FBYyxHQUFHLEVBQUUsQ0FBQztJQUN4QixJQUFJLFNBQVMsR0FBRyxDQUFFLENBQUMsRUFBRSxDQUFDLEVBQUUsQ0FBQyxFQUFFLENBQUMsRUFBRSxDQUFDLEVBQUUsQ0FBQyxDQUFFLENBQUM7SUFDckMsY0FBYyxDQUFDLElBQUksQ0FBQyxTQUFTLENBQUMsQ0FBQztJQUUvQixLQUFLLElBQUksS0FBSyxHQUFHLENBQUMsRUFBRSxLQUFLLEdBQUcsU0FBUyxDQUFDLE9BQU8sQ0FBQyxNQUFNLEVBQUUsS0FBSyxFQUFFLEVBQUU7UUFDM0QsSUFBSSxTQUFTLEdBQUcsU0FBUyxDQUFDLFNBQVMsQ0FBQyxLQUFLLENBQUMsQ0FBQztRQUVuRCx1RkFBdUY7UUFDdkYsNkJBQTZCO1FBRTdCLE9BQU8sQ0FBQyxHQUFHLENBQUMsR0FBRyxNQUFNLENBQUMsT0FBTyxDQUFDLEtBQUssQ0FBQyxHQUFHLENBQUMsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLEtBQUssU0FBUyxDQUFDLE9BQU8sQ0FBQyxLQUFLLENBQUMsQ0FBQyxJQUFJLFNBQVMsRUFBRSxDQUFDLENBQUM7UUFFcEcsSUFBSSxTQUFTLENBQUMsT0FBTyxDQUFDLEtBQUssQ0FBQyxLQUFLLEtBQUssQ0FBQyxHQUFHLENBQUMsT0FBTztZQUM5QyxTQUFTLEdBQUcsY0FBYyxDQUFDLEdBQUcsRUFBRSxDQUFDO2FBQ2hDLElBQUksU0FBUyxDQUFDLE9BQU8sQ0FBQyxLQUFLLENBQUMsS0FBSyxLQUFLLENBQUMsR0FBRyxDQUFDLElBQUk7WUFDaEQsY0FBYyxDQUFDLElBQUksQ0FBQyxTQUFTLENBQUMsQ0FBQzthQUM5QixJQUFJLFNBQVMsQ0FBQyxPQUFPLENBQUMsS0FBSyxDQUFDLEtBQUssS0FBSyxDQUFDLEdBQUcsQ0FBQyxTQUFTO1lBQ3JELFNBQVMsR0FBRyxLQUFLLENBQUMsSUFBSSxDQUFDLFNBQVMsQ0FBQyxTQUFTLEVBQUUsU0FBUyxDQUFDLENBQUM7YUFDdEQsSUFBSSxTQUFTLENBQUMsT0FBTyxDQUFDLEtBQUssQ0FBQyxLQUFLLEtBQUssQ0FBQyxHQUFHLENBQUMsYUFBYSxFQUFFO1lBQzNELElBQUksYUFBYSxFQUFFLEVBQUcsa0RBQWtEO2dCQUNwRSxJQUFJLGFBQWEsR0FBRyxDQUFDLENBQUM7Z0JBQ3RCLEtBQUssSUFBSSxjQUFjLEdBQUcsQ0FBQyxFQUFFLGNBQWMsR0FBRyxTQUFTLENBQUMsQ0FBQyxDQUFDLENBQUMsTUFBTSxFQUFFLGNBQWMsRUFBRSxFQUFFO29CQUNqRixJQUFJLFNBQVMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxjQUFjLENBQUMsS0FBSyxLQUFLLENBQUMsR0FBRyxDQUFDLE1BQU0sRUFBRyxjQUFjO3dCQUNsRSxhQUFhLElBQUksQ0FBQyxDQUFDO3lCQUNsQixJQUFJLFNBQVMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxjQUFjLENBQUMsS0FBSyxLQUFLLENBQUMsR0FBRyxDQUFDLE1BQU0sRUFBRyxjQUFjO3dCQUN2RSxhQUFhLElBQUksQ0FBQyxDQUFDO3lCQUNsQixJQUFJLFNBQVMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxjQUFjLENBQUMsS0FBSyxLQUFLLENBQUMsR0FBRyxDQUFDLFNBQVMsRUFBRSxFQUFHLGlCQUFpQjt3QkFDL0UsSUFBSSxFQUFFLEdBQUcsU0FBUyxDQUFDLENBQUMsQ0FBQyxDQUFDLGFBQWEsRUFBRSxDQUFDLENBQUM7d0JBQ3ZDLElBQUksRUFBRSxHQUFHLFNBQVMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxhQUFhLEVBQUUsQ0FBQyxDQUFDO3dCQUN2QyxJQUFJLEtBQUssR0FBRyxTQUFTLENBQUMsQ0FBQyxDQUFDLENBQUMsYUFBYSxFQUFFLENBQUMsQ0FBQzt3QkFDMUMsSUFBSSxNQUFNLEdBQUcsU0FBUyxDQUFDLENBQUMsQ0FBQyxDQUFDLGFBQWEsRUFBRSxDQUFDLENBQUM7d0JBQzNDLElBQUksRUFBRSxHQUFHLEVBQUUsR0FBRyxLQUFLLENBQUM7d0JBQ3BCLElBQUksRUFBRSxHQUFHLEVBQUUsR0FBRyxNQUFNLENBQUM7d0JBQ3JCLENBQUMsRUFBRSxFQUFFLEVBQUUsQ0FBQyxHQUFHLEtBQUssQ0FBQyxJQUFJLENBQUMsY0FBYyxDQUFDLENBQUMsRUFBRSxFQUFFLEVBQUUsQ0FBQyxFQUFFLFNBQVMsQ0FBQyxDQUFDO3dCQUMxRCxDQUFDLEVBQUUsRUFBRSxFQUFFLENBQUMsR0FBRyxLQUFLLENBQUMsSUFBSSxDQUFDLGNBQWMsQ0FBQyxDQUFDLEVBQUUsRUFBRSxFQUFFLENBQUMsRUFBRSxTQUFTLENBQUMsQ0FBQzt3QkFDMUQsS0FBSyxHQUFHLEVBQUUsR0FBRyxFQUFFLENBQUM7d0JBQ2hCLE1BQU0sR0FBRyxFQUFFLEdBQUcsRUFBRSxDQUFDO3dCQUNqQixpQkFBaUIsR0FBRyxFQUFFLENBQUMsRUFBRSxFQUFFLEVBQUUsQ0FBQyxFQUFFLEVBQUUsRUFBRSxLQUFLLEVBQUUsS0FBSyxFQUFFLE1BQU0sRUFBRSxNQUFNLEVBQUUsQ0FBQztxQkFDdEU7aUJBQ0o7YUFDSjtpQkFBTSxFQUFHLGtEQUFrRDtnQkFDeEQsSUFBSSxFQUFFLEdBQUcsU0FBUyxDQUFDO2dCQUNuQixJQUFJLEVBQUUsR0FBRyxTQUFTLENBQUM7Z0JBQ25CLElBQUksRUFBRSxHQUFHLFNBQVMsQ0FBQztnQkFDbkIsSUFBSSxFQUFFLEdBQUcsU0FBUyxDQUFDO2dCQUNuQixJQUFJLGFBQWEsR0FBRyxDQUFDLENBQUM7Z0JBQ3RCLEtBQUssSUFBSSxjQUFjLEdBQUcsQ0FBQyxFQUFFLGNBQWMsR0FBRyxTQUFTLENBQUMsQ0FBQyxDQUFDLENBQUMsTUFBTSxFQUFFLGNBQWMsRUFBRSxFQUFFO29CQUNqRixJQUFJLFNBQVMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxjQUFjLENBQUMsS0FBSyxLQUFLLENBQUMsR0FBRyxDQUFDLE1BQU0sRUFBRSxFQUFHLGNBQWM7d0JBQ3BFLEVBQUUsR0FBRyxTQUFTLENBQUMsQ0FBQyxDQUFDLENBQUMsYUFBYSxFQUFFLENBQUMsQ0FBQzt3QkFDbkMsRUFBRSxHQUFHLFNBQVMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxhQUFhLEVBQUUsQ0FBQyxDQUFDO3FCQUN0Qzt5QkFBTSxJQUFJLFNBQVMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxjQUFjLENBQUMsS0FBSyxLQUFLLENBQUMsR0FBRyxDQUFDLE1BQU0sRUFBRSxFQUFHLGNBQWM7d0JBQzNFLElBQUksQ0FBQyxhQUFhLEdBQUcsQ0FBQyxDQUFDLEtBQUssQ0FBQyxFQUFFLEVBQUcsMEZBQTBGOzRCQUN4SCxFQUFFLEdBQUcsU0FBUyxDQUFDLENBQUMsQ0FBQyxDQUFDLGFBQWEsRUFBRSxDQUFDLENBQUM7NEJBQ25DLEVBQUUsR0FBRyxTQUFTLENBQUMsQ0FBQyxDQUFDLENBQUMsYUFBYSxFQUFFLENBQUMsQ0FBQzt5QkFDdEM7NkJBQU07NEJBQ0gsYUFBYSxJQUFJLENBQUMsQ0FBQzt5QkFDdEI7cUJBQ0o7eUJBQU0sSUFBSSxTQUFTLENBQUMsQ0FBQyxDQUFDLENBQUMsY0FBYyxDQUFDLEtBQUssS0FBSyxDQUFDLEdBQUcsQ0FBQyxTQUFTLEVBQUUsRUFBRyxpQkFBaUI7d0JBQ2pGLElBQUksRUFBRSxLQUFLLFNBQVMsSUFBSSxFQUFFLEtBQUssU0FBUzs0QkFDcEMsT0FBTyxDQUFDLEdBQUcsQ0FBQyxtRkFBbUYsQ0FBQyxDQUFDOzZCQUNoRyxJQUFJLEVBQUUsS0FBSyxTQUFTLElBQUksRUFBRSxLQUFLLFNBQVM7NEJBQ3pDLE9BQU8sQ0FBQyxHQUFHLENBQUMsNEhBQTRILEVBQUUsS0FBSyxFQUFFLEtBQUssQ0FBQyxDQUFDOzZCQUN2Sjs0QkFDRCxDQUFDLEVBQUUsRUFBRSxFQUFFLENBQUMsR0FBRyxLQUFLLENBQUMsSUFBSSxDQUFDLGNBQWMsQ0FBQyxDQUFDLEVBQUUsRUFBRSxFQUFFLENBQUMsRUFBRSxTQUFTLENBQUMsQ0FBQzs0QkFDMUQsQ0FBQyxFQUFFLEVBQUUsRUFBRSxDQUFDLEdBQUcsS0FBSyxDQUFDLElBQUksQ0FBQyxjQUFjLENBQUMsQ0FBQyxFQUFFLEVBQUUsRUFBRSxDQUFDLEVBQUUsU0FBUyxDQUFDLENBQUM7NEJBQzFELElBQUksS0FBSyxHQUFHLElBQUksQ0FBQyxHQUFHLENBQUMsRUFBRSxHQUFHLEVBQUUsQ0FBQyxDQUFDOzRCQUM5QixJQUFJLE1BQU0sR0FBRyxJQUFJLENBQUMsR0FBRyxDQUFDLEVBQUUsR0FBRyxFQUFFLENBQUMsQ0FBQzs0QkFDL0IsS0FBSyxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUMsRUFBRSxFQUFFLEVBQUUsQ0FBQyxFQUFFLEVBQUUsRUFBRSxLQUFLLEVBQUUsS0FBSyxFQUFFLE1BQU0sRUFBRSxNQUFNLEVBQUUsQ0FBQyxDQUFDOzRCQUMzRCxFQUFFLEdBQUcsU0FBUyxDQUFDOzRCQUNmLEVBQUUsR0FBRyxTQUFTLENBQUM7NEJBQ2YsRUFBRSxHQUFHLFNBQVMsQ0FBQzs0QkFDZixFQUFFLEdBQUcsU0FBUyxDQUFDO3lCQUNsQjtxQkFDSjtpQkFDSjthQUNKO1NBQ0o7YUFBTSxJQUFJLGFBQWEsSUFBSSxpQkFBaUIsS0FBSyxTQUFTLElBQUksQ0FBQyxTQUFTLENBQUMsT0FBTyxDQUFDLEtBQUssQ0FBQyxLQUFLLEtBQUssQ0FBQyxHQUFHLENBQUMsSUFBSSxJQUFJLFNBQVMsQ0FBQyxPQUFPLENBQUMsS0FBSyxDQUFDLEtBQUssS0FBSyxDQUFDLEdBQUcsQ0FBQyxNQUFNLENBQUMsRUFBRTtZQUMzSixLQUFLLENBQUMsSUFBSSxDQUFDLGlCQUFpQixDQUFDLENBQUM7WUFDOUIsaUJBQWlCLEdBQUcsU0FBUyxDQUFDO1NBQ2pDO1FBQ1QsMkhBQTJIO1FBQzNILDRDQUE0QztRQUM1Qyw0Q0FBNEM7UUFDNUMsV0FBVztLQUNOO0lBRUwsT0FBTyxDQUFDLEdBQUcsQ0FBQyxTQUFTLEtBQUssQ0FBQyxNQUFNLFdBQVcsQ0FBQyxDQUFDO0lBQzlDLEtBQUssSUFBSSxJQUFJLElBQUksS0FBSztRQUNsQixPQUFPLENBQUMsR0FBRyxDQUFDLDZCQUE2QixJQUFJLENBQUMsQ0FBQyxNQUFNLElBQUksQ0FBQyxDQUFDLE1BQU0sSUFBSSxDQUFDLEtBQUssTUFBTSxJQUFJLENBQUMsTUFBTSxzQkFBc0IsQ0FBQyxDQUFDO0lBRXBILDhGQUE4RjtJQUM5Riw2RkFBNkY7SUFDN0YsOEZBQThGO0lBQzlGLHlFQUF5RTtJQUV6RSxJQUFJLGVBQWUsR0FBZ0IsRUFBRSxDQUFDO0lBQ3RDLElBQUksYUFBYSxHQUFnQixFQUFFLENBQUM7SUFFcEMsS0FBSyxJQUFJLElBQUksSUFBSSxLQUFLLEVBQUU7UUFDcEIsSUFBSSxJQUFJLENBQUMsTUFBTSxJQUFJLFNBQVMsSUFBSSxJQUFJLENBQUMsS0FBSyxJQUFJLEVBQUUsRUFBRyxvQkFBb0I7WUFDbkUsZUFBZSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQzthQUMxQixJQUFJLElBQUksQ0FBQyxLQUFLLElBQUksU0FBUyxJQUFJLElBQUksQ0FBQyxNQUFNLElBQUksRUFBRSxFQUFHLGtCQUFrQjtZQUN0RSxhQUFhLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDO0tBQ2hDO0lBRUQsSUFBSSxvQkFBb0IsR0FBRyxDQUFDLENBQUMsRUFBRSxDQUFDLEVBQUUsRUFBRSxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLEdBQUcsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUM7SUFDOUUsYUFBYSxDQUFDLElBQUksQ0FBQyxvQkFBb0IsQ0FBQyxDQUFDO0lBQ3pDLE9BQU8sQ0FBQyxHQUFHLENBQUMsU0FBUyxhQUFhLENBQUMsTUFBTSxvQkFBb0IsQ0FBQyxDQUFDO0lBRS9ELElBQUksc0JBQXNCLEdBQUcsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxFQUFFLEVBQUUsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLEdBQUcsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDO0lBQ2hGLGVBQWUsQ0FBQyxJQUFJLENBQUMsc0JBQXNCLENBQUMsQ0FBQztJQUM3QyxPQUFPLENBQUMsR0FBRyxDQUFDLFNBQVMsZUFBZSxDQUFDLE1BQU0sc0JBQXNCLENBQUMsQ0FBQztJQUVuRSw2Q0FBNkM7SUFFN0MsSUFBSSxNQUFNLEdBQVksRUFBRSxDQUFDO0lBRXpCLEtBQUssSUFBSSxJQUFJLElBQUksZUFBZSxFQUFFO1FBQzlCLElBQUksS0FBSyxHQUFHLEVBQUUsQ0FBQyxFQUFFLElBQUksQ0FBQyxDQUFDLEVBQUUsQ0FBQyxFQUFFLElBQUksQ0FBQyxDQUFDLEVBQUUsQ0FBQztRQUNyQyxJQUFJLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxVQUFVLENBQUMsRUFBRSxDQUFDLENBQUMsS0FBSyxDQUFDLENBQUMsR0FBRyxVQUFVLENBQUMsQ0FBQyxDQUFDLElBQUksQ0FBQyxHQUFHLENBQUMsS0FBSyxDQUFDLENBQUMsR0FBRyxVQUFVLENBQUMsQ0FBQyxDQUFDLElBQUksQ0FBQyxHQUFHLFNBQVMsSUFBSSxDQUFDLENBQUM7WUFDMUcsTUFBTSxDQUFDLElBQUksQ0FBQyxLQUFLLENBQUMsQ0FBQztRQUN2QixLQUFLLEdBQUcsRUFBRSxDQUFDLEVBQUUsSUFBSSxDQUFDLENBQUMsR0FBRyxJQUFJLENBQUMsS0FBSyxFQUFFLENBQUMsRUFBRSxJQUFJLENBQUMsQ0FBQyxFQUFFLENBQUM7UUFDOUMsSUFBSSxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsVUFBVSxDQUFDLEVBQUUsQ0FBQyxDQUFDLEtBQUssQ0FBQyxDQUFDLEdBQUcsVUFBVSxDQUFDLENBQUMsQ0FBQyxJQUFJLENBQUMsR0FBRyxDQUFDLEtBQUssQ0FBQyxDQUFDLEdBQUcsVUFBVSxDQUFDLENBQUMsQ0FBQyxJQUFJLENBQUMsR0FBRyxTQUFTLElBQUksQ0FBQyxDQUFDO1lBQzFHLE1BQU0sQ0FBQyxJQUFJLENBQUMsS0FBSyxDQUFDLENBQUM7S0FDMUI7SUFFRCxLQUFLLElBQUksSUFBSSxJQUFJLGFBQWEsRUFBRTtRQUM1QixJQUFJLEtBQUssR0FBRyxFQUFFLENBQUMsRUFBRSxJQUFJLENBQUMsQ0FBQyxFQUFFLENBQUMsRUFBRSxJQUFJLENBQUMsQ0FBQyxFQUFFLENBQUM7UUFDckMsSUFBSSxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsVUFBVSxDQUFDLEVBQUUsQ0FBQyxDQUFDLEtBQUssQ0FBQyxDQUFDLEdBQUcsVUFBVSxDQUFDLENBQUMsQ0FBQyxJQUFJLENBQUMsR0FBRyxDQUFDLEtBQUssQ0FBQyxDQUFDLEdBQUcs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